#![doc = include_str!("../README.md")]
#![no_std]

mod iter;
mod util;

extern crate alloc;

use alloc::alloc::{Layout, alloc, dealloc, handle_alloc_error};
use core::cell::Cell;
use core::marker::PhantomData;
use core::mem::{align_of, size_of};
use core::ptr::{self, NonNull};

pub struct Stack<T> {
    /// The current chunk we are bump allocating within.
    ///
    /// Its `next` link can point to the dead chunk, or to the cached chunk.
    ///
    /// Its `prev` link can point to the dead chunk or to the earlier allocated
    /// chunk.
    current_footer: Cell<NonNull<ChunkFooter>>,

    /// The first chunk we allocated, or the dead chunk if we haven't allocated
    /// anything yet.
    first_footer: Cell<NonNull<ChunkFooter>>,

    /// The capacity of the stack in elements.
    capacity: Cell<usize>,

    /// The number of elements currently in the stack.
    length: Cell<usize>,

    _phantom: PhantomData<T>,
}

// Public API
impl<T> Stack<T> {
    /// Constructs a new, empty `Stack<T>`.
    ///
    /// The stack will not allocate until elements are pushed onto it.
    ///
    /// # Examples
    ///
    /// ```
    /// use bump_stack::Stack;
    ///
    /// let mut stack: Stack<i32> = Stack::new();
    /// ```
    pub const fn new() -> Self {
        Self {
            current_footer: Cell::new(DEAD_CHUNK.get()),
            first_footer: Cell::new(DEAD_CHUNK.get()),
            capacity: Cell::new(0),
            length: Cell::new(0),
            _phantom: PhantomData,
        }
    }

    /// Constructs a new, empty `Stack<T>` with at least the specified capacity.
    ///
    /// The stack will be able to hold at least `capacity` elements without new
    /// allocations. This method is allowed to allocate for more elements than
    /// `capacity`. If `capacity` is zero, the stack will not allocate.
    ///
    /// If it is important to know the exact allocated capacity of a `Stack`,
    /// always use the [`capacity`] method after construction.
    ///
    /// For `Stack<T>` where `T` is a zero-sized type, there will be no
    /// allocation and the capacity will always be `usize::MAX`.
    ///
    /// [`capacity`]: Stack::capacity
    ///
    /// # Panics
    ///
    /// Panics if the `capacity` exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bump_stack::Stack;
    /// let mut stk = Stack::with_capacity(10);
    ///
    /// // The stack contains no items, even though it has capacity for more
    /// assert_eq!(stk.len(), 0);
    /// assert!(stk.capacity() >= 10);
    ///
    /// // These are all done without additional allocations...
    /// for i in 0..10 {
    ///     stk.push(i);
    /// }
    /// assert_eq!(stk.len(), 10);
    /// assert!(stk.capacity() >= 10);
    ///
    /// // ...but this may make the stack allocate a new chunk
    /// stk.push(11);
    /// assert_eq!(stk.len(), 11);
    /// assert!(stk.capacity() >= 11);
    ///
    /// // A stack of a zero-sized type will always over-allocate, since no
    /// // allocation is necessary
    /// let stk_units = Stack::<()>::with_capacity(10);
    /// assert_eq!(stk_units.capacity(), usize::MAX);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        let stack = Self::new();
        debug_assert!(unsafe { stack.current_footer.get().as_ref().is_dead() });
        if const { Self::ELEMENT_SIZE != 0 } && capacity != 0 {
            let chunk_size = Self::chunk_size_for(capacity);
            let footer = unsafe { stack.alloc_chunk(chunk_size) };
            stack.current_footer.set(footer);
            stack.first_footer.set(footer);
        }
        stack
    }

    /// Returns the total number of elements the stack can hold without
    /// additional allocations.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bump_stack::Stack;
    /// let mut stk = Stack::with_capacity(10);
    /// stk.push(42);
    /// assert!(stk.capacity() >= 10);
    /// ```
    ///
    /// A stack with zero-sized elements will always have a capacity of
    /// `usize::MAX`:
    ///
    /// ```
    /// # use bump_stack::Stack;
    /// #[derive(Clone)]
    /// struct ZeroSized;
    ///
    /// assert_eq!(std::mem::size_of::<ZeroSized>(), 0);
    /// let stk = Stack::<ZeroSized>::with_capacity(0);
    /// assert_eq!(stk.capacity(), usize::MAX);
    /// ```
    #[inline]
    pub const fn capacity(&self) -> usize {
        if const { Self::ELEMENT_SIZE == 0 } {
            usize::MAX
        } else {
            self.capacity.get()
        }
    }

    /// Returns the number of elements in the stack.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bump_stack::Stack;
    /// let stk = Stack::from([1, 2, 3]);
    /// assert_eq!(stk.len(), 3);
    /// ```
    #[inline]
    pub const fn len(&self) -> usize {
        self.length.get()
    }

    /// Returns `true` if the stack contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bump_stack::Stack;
    /// let mut s = Stack::new();
    /// assert!(s.is_empty());
    ///
    /// s.push(1);
    /// assert!(!s.is_empty());
    /// ```
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a reference to the first element of the stack, or `None` if it
    /// is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bump_stack::Stack;
    /// let mut s = Stack::new();
    /// assert_eq!(None, s.first());
    ///
    /// s.push(42);
    /// assert_eq!(Some(&42), s.first());
    /// ```
    #[inline]
    #[must_use]
    pub fn first(&self) -> Option<&T> {
        if !self.is_empty() {
            unsafe { Some(self.first_unchecked().as_mut()) }
        } else {
            None
        }
    }

    /// Returns a mutable reference to the first element of the slice, or `None`
    /// if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bump_stack::Stack;
    /// let mut s = Stack::new();
    /// assert_eq!(None, s.first_mut());
    ///
    /// s.push(1);
    /// if let Some(first) = s.first_mut() {
    ///     *first = 5;
    /// }
    /// assert_eq!(s.first(), Some(&5));
    /// ```
    #[inline]
    #[must_use]
    pub fn first_mut(&mut self) -> Option<&mut T> {
        if !self.is_empty() {
            unsafe { Some(self.first_unchecked().as_mut()) }
        } else {
            None
        }
    }

    /// Returns the reference to last element of the stack, or `None` if it is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bump_stack::Stack;
    /// let mut stk = Stack::new();
    /// assert_eq!(None, stk.last());
    ///
    /// stk.push(1);
    /// assert_eq!(Some(&1), stk.last());
    /// ```
    #[inline]
    #[must_use]
    pub fn last(&self) -> Option<&T> {
        if !self.is_empty() {
            unsafe { Some(self.last_unchecked().as_ref()) }
        } else {
            None
        }
    }
    /// Returns a mutable reference to the last item in the stack, or `None` if
    /// it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bump_stack::Stack;
    /// let mut stk = Stack::new();
    /// assert_eq!(None, stk.last_mut());
    ///
    /// stk.push(5);
    /// assert_eq!(Some(&mut 5), stk.last_mut());
    ///
    /// if let Some(last) = stk.last_mut() {
    ///     *last = 10;
    /// }
    /// assert_eq!(Some(&mut 10), stk.last_mut());
    /// ```
    #[inline]
    #[must_use]
    pub fn last_mut(&mut self) -> Option<&mut T> {
        if !self.is_empty() {
            unsafe { Some(self.last_unchecked().as_mut()) }
        } else {
            None
        }
    }

    /// Appends an element to the stack returning a reference to it.
    ///
    /// # Panics
    ///
    /// Panics if the global allocator cannot allocate a new chunk of memory.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bump_stack::Stack;
    /// let stk = Stack::new();
    /// let new_element = stk.push(3);
    ///
    /// assert_eq!(new_element, &3);
    /// assert_eq!(stk, [3]);
    /// ```
    ///
    /// # Time complexity
    ///
    /// Takes amortized *O*(1) time. If the stack's current chunk of memory is
    /// exhausted, it tries to use the cached one if it exists, otherwise it
    /// tries to allocate a new chunk.
    ///
    /// If the new chunk of memory is too big, it tries to divide the capacity
    /// by two and allocate it again until it reaches the minimum capacity. If
    /// it does, it panics.
    #[inline]
    pub fn push(&self, value: T) -> &T {
        self.push_with(|| value)
    }

    /// Pre-allocate space for an element in this stack, initializes it using
    /// the closure, and returns a reference to the new element.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bump_stack::Stack;
    /// let stk = Stack::new();
    /// let new_element = stk.push_with(|| 3);
    ///
    /// assert_eq!(new_element, &3);
    /// assert_eq!(stk, [3]);
    /// ```
    ///
    /// # Time complexity
    ///
    /// Takes amortized *O*(1) time. If the stack's current chunk of memory is
    /// exhausted, it tries to use the cached one if it exists, otherwise it
    /// tries to allocate a new chunk.
    ///
    /// If the new chunk of memory is too big, it tries to divide the capacity
    /// by two and allocate it again until it reaches the minimum capacity. If
    /// it does, it panics.
    #[inline(always)]
    pub fn push_with<F>(&self, f: F) -> &T
    where
        F: FnOnce() -> T,
    {
        unsafe {
            let p = self.alloc_element();
            util::write_with(p.as_ptr(), f);
            self.length.update(|len| len + 1);
            p.as_ref()
        }
    }

    /// Removes the last element from a vector and returns it, or [`None`] if it
    /// is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bump_stack::Stack;
    /// let mut stk = Stack::from([1, 2, 3]);
    /// assert_eq!(stk.pop(), Some(3));
    /// assert_eq!(stk, [2, 1]);
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        unsafe {
            if let Some(element_ptr) = self.dealloc_element() {
                if const { Self::ELEMENT_SIZE == 0 } && self.length.get() == 0 {
                    None
                } else {
                    self.length.update(|len| len - 1);
                    Some(ptr::read(element_ptr.as_ptr()))
                }
            } else {
                None
            }
        }
    }

    /// Clears the stack, removing all elements.
    ///
    /// This method leaves the biggest chunk of memory for future allocations.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bump_stack::Stack;
    /// let mut stk = Stack::from([1, 2, 3]);
    ///
    /// stk.clear();
    ///
    /// assert!(stk.is_empty());
    /// assert!(stk.capacity() > 0);
    /// ```
    pub fn clear(&mut self) {
        // TODO: Reimplement the method running `drop_in_place`
        while let Some(elem) = self.pop() {
            drop(elem)
        }
    }

    /// Returns an iterator over the stack.
    ///
    /// The iterator yields all items' references in inverted order of their
    /// insertion, corresponding to the LIFO order.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bump_stack::Stack;
    /// let stk = Stack::from([1, 2, 4]);
    /// let mut iterator = stk.iter();
    ///
    /// assert_eq!(iterator.next(), Some(&4));
    /// assert_eq!(iterator.next(), Some(&2));
    /// assert_eq!(iterator.next(), Some(&1));
    /// assert_eq!(iterator.next(), None);
    /// ```
    ///
    /// Since `Stack` allows to push new elements using immutable reference to
    /// itself, you can push during iteration. But iteration is running over
    /// elements existing at the moment of the iterator creating. It guarantees
    /// that you won't get infinite loop.
    ///
    /// ```
    /// # use bump_stack::Stack;
    /// let stk = Stack::from([1, 2, 4]);
    ///
    /// for elem in stk.iter() {
    ///     stk.push(*elem);
    /// }
    /// assert_eq!(stk.len(), 6);
    /// assert_eq!(stk, [1, 2, 4, 4, 2, 1]);
    /// ```
    pub fn iter(&self) -> impl core::iter::DoubleEndedIterator<Item = &T> {
        crate::iter::Iter::new(self)
    }
}

impl<T> core::default::Default for Stack<T> {
    /// Creates an empty `Stack<T>`.
    ///
    /// The stack will not allocate until elements are pushed onto it.
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const N: usize> core::convert::From<&[T; N]> for Stack<T>
where
    T: Clone,
{
    /// Creates a `Stack<T>` with a chunk big enough to contain N items and
    /// fills it by cloning `slice`'s items.
    fn from(slice: &[T; N]) -> Self {
        let stk = Stack::with_capacity(N);
        for item in slice {
            stk.push(item.clone());
        }
        stk
    }
}

impl<T, const N: usize> core::convert::From<&mut [T; N]> for Stack<T>
where
    T: Clone,
{
    /// Creates a `Stack<T>` with a chunk big enough to contain N items and
    /// fills it by cloning `slice`'s items.
    #[inline]
    fn from(slice: &mut [T; N]) -> Self {
        core::convert::From::<&[T; N]>::from(slice)
    }
}

impl<T, const N: usize> core::convert::From<[T; N]> for Stack<T>
where
    T: Clone,
{
    /// Creates a `Stack<T>` with a chunk big enough to contain N items and
    /// fills it by cloning `array`'s items.
    #[inline]
    fn from(array: [T; N]) -> Self {
        core::convert::From::<&[T; N]>::from(&array)
    }
}

impl<T> core::convert::From<&[T]> for Stack<T>
where
    T: Clone,
{
    /// Creates a `Stack<T>` with a chunk big enough to contain N items and
    /// fills it by cloning `slice`'s items.
    fn from(slice: &[T]) -> Self {
        let stk = Stack::with_capacity(slice.len());
        for item in slice {
            stk.push(item.clone());
        }
        stk
    }
}

impl<T> core::convert::From<&mut [T]> for Stack<T>
where
    T: Clone,
{
    /// Creates a `Stack<T>` with a chunk big enough to contain N items and
    /// fills it by cloning `slice`'s items.
    fn from(slice: &mut [T]) -> Self {
        core::convert::From::<&[T]>::from(slice)
    }
}

impl<T> core::ops::Drop for Stack<T> {
    fn drop(&mut self) {
        self.clear();
        unsafe {
            let current_footer = self.current_footer.get().as_ref();
            if !current_footer.is_dead() {
                debug_assert!(current_footer.prev.get().as_ref().is_dead());
                debug_assert!(current_footer.next.get().as_ref().is_dead());
                self.dealloc_chunk(self.current_footer.get());
            }
        }
    }
}

impl<'a, T> core::iter::IntoIterator for &'a Stack<T> {
    type Item = &'a T;
    type IntoIter = crate::iter::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        crate::iter::Iter::new(self)
    }
}

impl<T, U> core::cmp::PartialEq<[U]> for Stack<T>
where
    T: core::cmp::PartialEq<U>,
{
    fn eq(&self, other: &[U]) -> bool {
        self.len() == other.len() && self.iter().zip(other.iter()).all(|(a, b)| a == b)
    }
}

impl<T, U> core::cmp::PartialEq<&[U]> for Stack<T>
where
    T: core::cmp::PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &&[U]) -> bool {
        core::cmp::PartialEq::<[U]>::eq(self, other)
    }
}

impl<T, U> core::cmp::PartialEq<&mut [U]> for Stack<T>
where
    T: core::cmp::PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &&mut [U]) -> bool {
        core::cmp::PartialEq::<[U]>::eq(self, other)
    }
}

impl<T, U, const N: usize> core::cmp::PartialEq<[U; N]> for Stack<T>
where
    T: core::cmp::PartialEq<U>,
{
    fn eq(&self, other: &[U; N]) -> bool {
        self.len() == N && self.iter().zip(other.iter()).all(|(a, b)| a == b)
    }
}

impl<T, U, const N: usize> core::cmp::PartialEq<&[U; N]> for Stack<T>
where
    T: core::cmp::PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &&[U; N]) -> bool {
        core::cmp::PartialEq::<[U; N]>::eq(self, other)
    }
}

impl<T, U, const N: usize> core::cmp::PartialEq<&mut [U; N]> for Stack<T>
where
    T: core::cmp::PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &&mut [U; N]) -> bool {
        core::cmp::PartialEq::<[U; N]>::eq(self, other)
    }
}

impl<T, U, const N: usize> core::cmp::PartialEq<Stack<U>> for [T; N]
where
    T: core::cmp::PartialEq<U>,
{
    fn eq(&self, other: &Stack<U>) -> bool {
        self.len() == other.len() && self.iter().zip(other.iter()).all(|(a, b)| a == b)
    }
}

impl<T, U, const N: usize> core::cmp::PartialEq<Stack<U>> for &[T; N]
where
    T: core::cmp::PartialEq<U>,
{
    fn eq(&self, other: &Stack<U>) -> bool {
        *self == other
    }
}

impl<T, U, const N: usize> core::cmp::PartialEq<Stack<U>> for &mut [T; N]
where
    T: core::cmp::PartialEq<U>,
{
    fn eq(&self, other: &Stack<U>) -> bool {
        *self == other
    }
}

impl<T> core::fmt::Debug for Stack<T>
where
    T: core::fmt::Debug,
{
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// This footer is always at the end of the chunk. So memory available for
/// allocation is `self.data..=self`.
#[derive(Debug)]
struct ChunkFooter {
    /// Pointer to the start of this chunk allocation.
    data: NonNull<u8>,

    /// Bump allocation finger that is always in the range `self.data..=self`.
    ptr: Cell<NonNull<u8>>,

    /// The layout of this chunk's allocation.
    layout: Layout,

    /// Link to the previous chunk.
    ///
    /// Note that the last node in the `prev` linked list is the dead chunk,
    /// whose `prev` link points to itself.
    prev: Cell<NonNull<ChunkFooter>>,

    /// Link to the next chunk.
    ///
    /// Note that the last node in the `next` linked list is the dead chunk,
    /// whose `next` link points to itself.
    next: Cell<NonNull<ChunkFooter>>,
}

impl ChunkFooter {
    /// Returns a non-null pointer to the chunk footer.
    fn get(&self) -> NonNull<Self> {
        NonNull::from(self)
    }

    /// This is the `DEAD_CHUNK` chunk.
    fn is_dead(&self) -> bool {
        ptr::eq(self, &DEAD_CHUNK.0)
    }

    /// Returns the number of bytes occupied by the chunk: `end - ptr`.
    fn occupied(&self) -> usize {
        let ptr = self.ptr.get().as_ptr() as usize;
        let end = self.get().as_ptr() as usize;
        debug_assert!(ptr <= end);
        end - ptr
    }

    /// The capacity of the chunk in bytes.
    fn capacity(&self) -> usize {
        let end = self.get().as_ptr() as usize;
        let start = self.data.as_ptr() as usize;
        debug_assert!(start < end);
        end - start
    }

    /// Checks if the chunk is full.
    fn is_full(&self) -> bool {
        let start = self.data.as_ptr() as usize;
        let ptr = self.ptr.get().as_ptr() as usize;
        debug_assert!(start <= ptr);
        start == ptr
    }
}

#[repr(transparent)]
struct DeadChunkFooter(ChunkFooter);

unsafe impl Sync for DeadChunkFooter {}

impl DeadChunkFooter {
    const fn get(&'static self) -> NonNull<ChunkFooter> {
        unsafe { NonNull::new_unchecked(&DEAD_CHUNK as *const DeadChunkFooter as *mut ChunkFooter) }
    }
}

// Empty chunk that contains only its footer.
static DEAD_CHUNK: DeadChunkFooter = DeadChunkFooter(ChunkFooter {
    data: DEAD_CHUNK.get().cast(),
    ptr: Cell::new(DEAD_CHUNK.get().cast()),
    layout: Layout::new::<ChunkFooter>(),
    prev: Cell::new(DEAD_CHUNK.get()),
    next: Cell::new(DEAD_CHUNK.get()),
});

/// Maximum typical overhead per allocation imposed by allocators.
const ALLOC_OVERHEAD: usize = 16;

// Constants
impl<T> Stack<T> {
    /// Element alignment
    const ELEMENT_ALIGN: usize = align_of::<T>();

    /// Element size
    const ELEMENT_SIZE: usize = size_of::<T>();

    /// Is `true` if `T` is a zero-sized type.
    const ELEMENT_IS_ZST: bool = Self::ELEMENT_SIZE == 0;

    /// Footer alignment is maximum of element alignment and footer alignment
    /// itself. It allows to use footer's address as the `end` of the elements
    /// slice within the chunk.
    const FOOTER_ALIGN: usize = util::max(align_of::<ChunkFooter>(), Self::ELEMENT_ALIGN);

    /// Footer size.
    const FOOTER_SIZE: usize = size_of::<ChunkFooter>();

    /// Find out if it possible to use footer's address as the `end` of elements
    /// array within the chunk.
    const FOOTER_IS_END: bool = {
        assert!(util::is_aligned_to(Self::CHUNK_ALIGN, Self::ELEMENT_ALIGN));
        assert!(util::is_aligned_to(Self::CHUNK_ALIGN, Self::FOOTER_ALIGN));
        Self::FOOTER_ALIGN.is_multiple_of(Self::ELEMENT_SIZE)
            || Self::ELEMENT_SIZE.is_multiple_of(Self::FOOTER_ALIGN)
    };

    /// Chunk alignment is the maximum of element and footer alignments.
    const CHUNK_ALIGN: usize = util::max(Self::ELEMENT_ALIGN, Self::FOOTER_ALIGN);

    /// Chunk size enough for at least one element.
    const CHUNK_MIN_SIZE: usize = Self::chunk_size_for(1);

    /// Chunk size for the first chunk if capacity is not specified with
    /// [`Stack::with_capacity`].
    const CHUNK_FIRST_SIZE: usize = {
        let chunk_512b = 0x200 - ALLOC_OVERHEAD;
        let size = if Self::ELEMENT_SIZE > 1024 {
            Self::chunk_size_for(2)
        } else {
            util::max(chunk_512b, Self::chunk_size_for(8))
        };
        assert!((size + ALLOC_OVERHEAD).is_power_of_two());
        size
    };

    /// Maximal possible chunk size. Is equal to 4 GiB, if address space is not
    /// limited. Otherwise, it is equal to (address space size / 8).
    const CHUNK_MAX_SIZE: usize = {
        let part_of_entire_memory = util::round_down_to_pow2(isize::MAX as usize >> 2);
        let common_sensible_in_2025 = 4 << 30; // 4 GiB
        let size = util::min(part_of_entire_memory, common_sensible_in_2025);
        assert!(size.is_power_of_two());
        size - ALLOC_OVERHEAD
    };

    /// Calculate chunk size big enough for the given number of elements. The
    /// chunk is a power of two minus an allocator overhead.
    const fn chunk_size_for(mut elements_count: usize) -> usize {
        if elements_count < 2 {
            // I'm not sure that `alloc` always returns pointer aligned as
            // requested, so it's possible that the allocated memory for one
            // element is not enough for that element. So I'm increasing here
            // the requested size for at least two elements.
            elements_count = 2;
        }
        let mut chunk_size = elements_count * Self::ELEMENT_SIZE;
        assert!(util::is_aligned_to(chunk_size, Self::ELEMENT_ALIGN));

        let overhead = ALLOC_OVERHEAD + Self::FOOTER_SIZE;
        chunk_size += overhead.next_multiple_of(Self::FOOTER_ALIGN);

        chunk_size.next_power_of_two() - ALLOC_OVERHEAD
    }

    /// Checks if the chunk doesn't have any elements.
    #[inline(always)]
    fn chunk_is_empty(footer: &ChunkFooter) -> bool {
        let end = footer.get().as_ptr() as usize;
        let ptr = footer.ptr.get().as_ptr() as usize;
        debug_assert!(ptr <= end);
        if const { Self::FOOTER_IS_END } {
            end == ptr
        } else {
            end - ptr < Self::ELEMENT_SIZE
        }
    }
}

// Private API
impl<T> Stack<T> {
    #[inline(always)]
    unsafe fn alloc_element(&self) -> NonNull<T> {
        if let Some(ptr) = self.alloc_element_fast() {
            ptr
        } else {
            debug_assert!(!Self::ELEMENT_IS_ZST, "slow alloc is impossible for ZST");
            unsafe { self.alloc_element_slow() }
        }
    }

    #[inline(always)]
    fn alloc_element_fast(&self) -> Option<NonNull<T>> {
        let current_footer = unsafe { self.current_footer.get().as_ref() };

        if current_footer.is_full() && const { !Self::ELEMENT_IS_ZST } {
            return None;
        }

        let ptr = current_footer.ptr.get().as_ptr();
        let new_ptr = unsafe {
            let ptr = ptr.wrapping_byte_sub(Self::ELEMENT_SIZE);
            NonNull::new_unchecked(ptr)
        };
        current_footer.ptr.set(new_ptr);

        Some(new_ptr.cast())
    }

    // Should be run only if the current chunk is full
    unsafe fn alloc_element_slow(&self) -> NonNull<T> {
        unsafe {
            let current_footer = self.current_footer.get().as_ref();

            debug_assert!(current_footer.is_full());

            if current_footer.is_dead() {
                // this is initial state without allocated chunks at all
                debug_assert!(current_footer.is_dead());
                debug_assert!(current_footer.prev.get().as_ref().is_dead());
                debug_assert!(current_footer.next.get().as_ref().is_dead());

                let new_footer_ptr = self.alloc_chunk(Self::CHUNK_FIRST_SIZE);
                self.current_footer.set(new_footer_ptr);
                self.first_footer.set(new_footer_ptr);
            } else {
                // at least the current chunk is not dead
                let next_footer_ptr = current_footer.next.get();
                let next_footer = next_footer_ptr.as_ref();

                if next_footer.is_dead() {
                    // the current chunk is single, so create a new one, and
                    // make it the current chunk.
                    let current_chunk_size = current_footer.layout.size();
                    let new_chunk_size = if current_chunk_size == Self::CHUNK_MAX_SIZE {
                        Self::CHUNK_MAX_SIZE
                    } else {
                        debug_assert!(current_chunk_size < Self::CHUNK_MAX_SIZE);
                        ((current_chunk_size + ALLOC_OVERHEAD) << 1) - ALLOC_OVERHEAD
                    };

                    debug_assert!((new_chunk_size + ALLOC_OVERHEAD).is_power_of_two());

                    let new_footer_ptr = self.alloc_chunk(new_chunk_size);
                    let new_footer = new_footer_ptr.as_ref();

                    current_footer.next.set(new_footer_ptr);
                    new_footer.prev.set(self.current_footer.get());

                    self.current_footer.set(new_footer_ptr);
                } else {
                    // there is a next empty chunk, so make it the current chunk
                    debug_assert!(Self::chunk_is_empty(next_footer));
                    self.current_footer.set(next_footer_ptr);
                }
            }

            self.alloc_element_fast().unwrap_unchecked()
        }
    }

    /// Creates a new chunk with the given size. If it can't allocate a chunk
    /// with the given size, it tries to allocate a chunk with a two times
    /// smaller size. Otherwise, it panics.
    ///
    /// Properties `data`, `ptr`, and `layout` are initialized to the values
    /// of the newly allocated chunk.
    ///
    /// Properties `prev` and `next` point to the `DEAD_CHUNK`, so you should
    /// reinitialize them to needed values, if there exist another chunks in the
    /// list.
    unsafe fn alloc_chunk(&self, chunk_size: usize) -> NonNull<ChunkFooter> {
        debug_assert!(chunk_size <= Self::CHUNK_MAX_SIZE);

        let mut chunk_size = chunk_size;
        let chunk_align = Self::CHUNK_ALIGN;

        let (chunk_ptr, chunk_layout) = loop {
            // checks for `Layout::from_size_align_unchecked`
            debug_assert!(chunk_align != 0);
            debug_assert!(chunk_align.is_power_of_two());
            debug_assert!((chunk_size + ALLOC_OVERHEAD).is_power_of_two());
            debug_assert!(chunk_size <= isize::MAX as usize);

            let chunk_layout =
                unsafe { Layout::from_size_align_unchecked(chunk_size, chunk_align) };

            let chunk_ptr = unsafe { alloc(chunk_layout) };
            if !chunk_ptr.is_null() {
                assert!(util::ptr_is_aligned_to(chunk_ptr, Self::CHUNK_ALIGN));
                break (chunk_ptr, chunk_layout);
            }

            // if couldn't get a new chunk, try to shrink the chunk size by half
            chunk_size = ((chunk_size + ALLOC_OVERHEAD) >> 1) - ALLOC_OVERHEAD;
            if chunk_size < Self::CHUNK_MIN_SIZE {
                handle_alloc_error(chunk_layout);
            }
        };

        let chunk_start = chunk_ptr;
        let chunk_end = chunk_start.wrapping_byte_add(chunk_layout.size());
        let mut footer_addr = {
            let addr = chunk_end.wrapping_byte_sub(Self::FOOTER_SIZE);
            util::round_mut_ptr_down_to(addr, Self::FOOTER_ALIGN)
        };

        debug_assert!(chunk_start < footer_addr);
        debug_assert!(footer_addr < chunk_end);
        debug_assert!(util::ptr_is_aligned_to(chunk_start, Self::ELEMENT_ALIGN));

        let chunk_cap_in_bytes = footer_addr as usize - chunk_start as usize;
        let chunk_capacity = chunk_cap_in_bytes / Self::ELEMENT_SIZE;
        self.capacity.update(|cap| cap + chunk_capacity);

        let buffer_size = chunk_capacity * Self::ELEMENT_SIZE;
        let new_ptr = chunk_start.wrapping_byte_add(buffer_size);
        debug_assert!(new_ptr <= footer_addr);

        if const { Self::ELEMENT_SIZE.is_multiple_of(Self::FOOTER_ALIGN) } {
            // in this case we additionally align the footer address to the end
            // of the elements slice
            footer_addr = chunk_start.wrapping_byte_add(buffer_size);
        }

        if const { Self::FOOTER_IS_END } {
            debug_assert!(new_ptr == footer_addr);
        }

        unsafe {
            let footer_ptr = footer_addr as *mut ChunkFooter;
            util::write_with(footer_ptr, || ChunkFooter {
                data: NonNull::new_unchecked(chunk_start),
                ptr: Cell::new(NonNull::new_unchecked(new_ptr)),
                layout: chunk_layout,
                prev: Cell::new(DEAD_CHUNK.get()),
                next: Cell::new(DEAD_CHUNK.get()),
            });
            NonNull::new_unchecked(footer_ptr)
        }
    }

    #[inline(always)]
    unsafe fn dealloc_element(&mut self) -> Option<NonNull<T>> {
        unsafe {
            if let Some(ptr) = self.dealloc_element_fast() {
                Some(ptr)
            } else {
                self.dealloc_element_slow()
            }
        }
    }

    #[inline(always)]
    unsafe fn dealloc_element_fast(&mut self) -> Option<NonNull<T>> {
        let current_footer = unsafe { self.current_footer.get().as_ref() };

        let ptr = current_footer.ptr.get().as_ptr();
        let end = self.current_footer.get().as_ptr().cast();
        debug_assert!(ptr <= end);

        let capacity = end as usize - ptr as usize;
        if capacity < Self::ELEMENT_SIZE {
            return None;
        }

        let new_ptr = ptr.wrapping_byte_add(Self::ELEMENT_SIZE);

        debug_assert!(new_ptr <= end);
        debug_assert!(util::ptr_is_aligned_to(new_ptr, Self::ELEMENT_ALIGN));

        let new_ptr = unsafe { NonNull::new_unchecked(new_ptr) };
        current_footer.ptr.set(new_ptr);

        Some(unsafe { NonNull::new_unchecked(ptr.cast()) })
    }

    unsafe fn dealloc_element_slow(&mut self) -> Option<NonNull<T>> {
        unsafe {
            let current_footer_ptr = self.current_footer.get();
            let current_footer = current_footer_ptr.as_ref();

            let next_footer_ptr = current_footer.next.get();
            let next_footer = next_footer_ptr.as_ref();

            let prev_footer_ptr = current_footer.prev.get();
            let prev_footer = prev_footer_ptr.as_ref();

            if current_footer.is_dead() {
                debug_assert!(next_footer.is_dead());
                debug_assert!(prev_footer.is_dead());
                return None;
            }

            debug_assert!(Self::chunk_is_empty(current_footer));
            debug_assert!(Self::chunk_is_empty(next_footer));

            if !next_footer.is_dead() {
                if current_footer.layout.size() < next_footer.layout.size() {
                    debug_assert!(next_footer.next.get().as_ref().is_dead());

                    next_footer.prev.set(prev_footer_ptr);
                    self.current_footer.set(next_footer_ptr);

                    self.dealloc_chunk(current_footer_ptr);
                } else {
                    self.dealloc_chunk(next_footer_ptr);
                }
                self.current_footer
                    .get()
                    .as_ref()
                    .next
                    .set(DEAD_CHUNK.get());
            }

            if prev_footer.is_dead() {
                self.first_footer.set(self.current_footer.get());
                None
            } else {
                // check if prev_footer is full
                debug_assert!(prev_footer.is_full());

                prev_footer.next.set(self.current_footer.get());
                self.current_footer.set(prev_footer_ptr);

                self.dealloc_element_fast()
            }
        }
    }

    unsafe fn dealloc_chunk(&mut self, mut footer_ptr: NonNull<ChunkFooter>) {
        unsafe {
            let footer = footer_ptr.as_mut();
            let chunk_capacity = footer.capacity() / Self::ELEMENT_SIZE;
            debug_assert!(chunk_capacity <= self.capacity());
            self.capacity.update(|cap| cap - chunk_capacity);
            debug_assert!(self.len() <= self.capacity());
            dealloc(footer.data.as_ptr(), footer.layout);
        }
    }

    /// Returns a pointer to the first pushed element of the stack.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the stack is not empty.
    unsafe fn first_unchecked(&self) -> NonNull<T> {
        if const { Self::ELEMENT_IS_ZST } {
            debug_assert!(unsafe { self.first_footer.get().as_ref().is_dead() });
            return self.first_footer.get().cast();
        }
        unsafe {
            let first_footer = self.first_footer.get().as_ref();
            debug_assert!(first_footer.occupied() >= Self::ELEMENT_SIZE);

            let ptr = first_footer.ptr.get().as_ptr();
            let end = first_footer as *const ChunkFooter as *const u8;
            let elems_num = (end as usize - ptr as usize) / Self::ELEMENT_SIZE;

            NonNull::new_unchecked(ptr).cast().add(elems_num - 1)
        }
    }

    /// Returns a pointer to the last element of the stack.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the stack is not empty.
    unsafe fn last_unchecked(&self) -> NonNull<T> {
        if const { Self::ELEMENT_IS_ZST } {
            debug_assert!(unsafe { self.first_footer.get().as_ref().is_dead() });
            return self.first_footer.get().cast();
        }
        unsafe {
            let mut footer = self.current_footer.get().as_ref();
            if Self::chunk_is_empty(footer) {
                footer = footer.prev.get().as_ref();
            }
            debug_assert!(!Self::chunk_is_empty(footer));
            footer.ptr.get().cast()
        }
    }
}

/// Collection of static tests for inner constants of Stack. They are enabled
/// only for some platforms, where I could test them. Look inside to see which
/// ones exactly.
#[cfg(test)]
mod stest;

/// Unit tests.
#[cfg(test)]
mod utest;
