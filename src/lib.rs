#![no_std]

mod util;

extern crate alloc;

use alloc::alloc::{Layout, alloc, dealloc, handle_alloc_error};
use core::cell::Cell;
use core::marker::PhantomData;
use core::mem;
use core::ptr::{self, NonNull};

#[derive(Debug)]
pub struct Stack<T> {
    /// The current chunk we are bump allocating within.
    ///
    /// Its `next` link can point to the dead chunk, or to the cached chunk.
    ///
    /// Its `prev` link can point to the dead chunk or to the earlier allocated
    /// chunk.
    current_footer: NonNull<ChunkFooter>,

    /// The capacity of the stack in elements.
    capacity: usize,

    /// The number of elements currently in the stack.
    length: usize,

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
            current_footer: DEAD_CHUNK.get(),
            capacity: 0,
            length: 0,
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
        let mut stack = Self::new();
        debug_assert!(unsafe { stack.current_footer.as_ref().is_dead() });
        if capacity != 0 && Self::ELEMENT_SIZE != 0 {
            let chunk_size = Self::chunk_size_for(capacity);
            let footer = unsafe { stack.alloc_chunk(chunk_size) };
            stack.current_footer = footer;
        }
        stack
    }

    /// Returns the total number of elements the stack can hold without new
    /// allocating.
    #[inline]
    pub const fn capacity(&self) -> usize {
        if Self::ELEMENT_SIZE == 0 {
            usize::MAX
        } else {
            self.capacity
        }
    }

    /// Returns the total number of elements the stack can hold without
    /// additional allocations.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bump_stack::Stack;
    /// let mut stk: Stack<i32> = Stack::with_capacity(10);
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
    /// fn main() {
    ///     assert_eq!(std::mem::size_of::<ZeroSized>(), 0);
    ///     let stk = Stack::<ZeroSized>::with_capacity(0);
    ///     assert_eq!(stk.capacity(), usize::MAX);
    /// }
    /// ```
    #[inline]
    pub const fn len(&self) -> usize {
        self.length
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

    /// Appends an element to the stack.
    ///
    /// # Panics
    ///
    /// Panics if the global allocator cannot allocate a new chunk of memory.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bump_stack::Stack;
    /// let mut stk = Stack::<i32>::new();
    /// stk.push(3);
    /// //TODO: assert_eq!(stk, [1, 2, 3]);
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
    pub fn push(&mut self, value: T) {
        self.push_with(|| value);
    }

    #[inline(always)]
    pub fn push_with<F>(&mut self, f: F)
    where
        F: FnOnce() -> T,
    {
        unsafe {
            let p = self.alloc_element();
            util::write_with(p.as_ptr(), f);
        }
        self.length += 1;
    }

    pub fn pop(&mut self) -> Option<T> {
        unsafe {
            if let Some(element_ptr) = self.dealloc_element() {
                if Self::ELEMENT_SIZE == 0 && self.length == 0 {
                    None
                } else {
                    self.length -= 1;
                    Some(ptr::read(element_ptr.as_ptr()))
                }
            } else {
                None
            }
        }
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

impl<T> core::ops::Drop for Stack<T> {
    fn drop(&mut self) {
        while let Some(item) = self.pop() {
            drop(item);
        }
        unsafe {
            let current_footer = self.current_footer.as_ref();
            if !current_footer.is_dead() {
                debug_assert!(current_footer.prev.get().as_ref().is_dead());
                debug_assert!(current_footer.next.get().as_ref().is_dead());
                self.dealloc_chunk(self.current_footer);
            }
        }
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

#[repr(transparent)]
struct DeadChunkFooter(ChunkFooter);

unsafe impl Sync for DeadChunkFooter {}

impl DeadChunkFooter {
    const fn get(&'static self) -> NonNull<ChunkFooter> {
        unsafe { NonNull::new_unchecked(&DEAD_CHUNK as *const DeadChunkFooter as *mut ChunkFooter) }
    }
}

// Empty chunk that contains only its footer.
static DEAD_CHUNK: DeadChunkFooter = DeadChunkFooter(unsafe {
    ChunkFooter {
        data: NonNull::new_unchecked(&DEAD_CHUNK as *const DeadChunkFooter as *mut u8),
        ptr: Cell::new(NonNull::new_unchecked(
            &DEAD_CHUNK as *const DeadChunkFooter as *mut u8,
        )),
        layout: Layout::new::<ChunkFooter>(),
        prev: Cell::new(NonNull::new_unchecked(
            &DEAD_CHUNK as *const DeadChunkFooter as *mut ChunkFooter,
        )),
        next: Cell::new(NonNull::new_unchecked(
            &DEAD_CHUNK as *const DeadChunkFooter as *mut ChunkFooter,
        )),
    }
});

impl ChunkFooter {
    /// This is the `DEAD_CHUNK` chunk.
    fn is_dead(&self) -> bool {
        ptr::eq(self, &DEAD_CHUNK.0)
    }

    /// Amount of unoccupied bytes in the chunk.
    ///
    /// For a full chunk, it can be in the range of `0..ELEMENT_SIZE`.
    fn remains(&self) -> usize {
        let end = self as *const ChunkFooter as usize;
        let ptr = self.ptr.get().as_ptr() as usize;
        debug_assert!(ptr <= end);
        end - ptr
    }

    /// Amount of occupied bytes in the chunk.
    ///
    /// For an empty chunk, it can be in the range of `0..ELEMENT_SIZE`.
    fn occupied(&self) -> usize {
        let start = self.data.as_ptr() as usize;
        let ptr = self.ptr.get().as_ptr() as usize;
        debug_assert!(start <= ptr);
        ptr - start
    }

    /// The capacity of the chunk in bytes.
    fn capacity(&self) -> usize {
        let end = self as *const Self as usize;
        let start = self.data.as_ptr() as usize;
        debug_assert!(start < end);
        end - start
    }
}

/// Maximum typical overhead per allocation imposed by allocators.
const ALLOC_OVERHEAD: usize = 16;

// Constants
impl<T> Stack<T> {
    /// Element alignment
    const ELEMENT_ALIGN: usize = mem::align_of::<T>();

    /// Element size
    const ELEMENT_SIZE: usize = mem::size_of::<T>();

    const FOOTER_ALIGN: usize = mem::align_of::<ChunkFooter>();

    const FOOTER_SIZE: usize = mem::size_of::<ChunkFooter>();

    /// Chunk alignment is at least the maximum of element alignment and 8.
    const CHUNK_ALIGN: usize = util::max(Self::ELEMENT_ALIGN, 8);

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
        assert!(chunk_size.is_multiple_of(Self::ELEMENT_ALIGN));

        let overhead = ALLOC_OVERHEAD + Self::FOOTER_SIZE;
        chunk_size += overhead.next_multiple_of(Self::FOOTER_ALIGN);

        chunk_size.next_power_of_two() - ALLOC_OVERHEAD
    }
}

// Private API
impl<T> Stack<T> {
    unsafe fn alloc_element(&mut self) -> NonNull<T> {
        if let Some(ptr) = self.alloc_element_fast() {
            ptr
        } else {
            unsafe { self.alloc_element_slow() }
        }
    }

    fn alloc_element_fast(&self) -> Option<NonNull<T>> {
        let current_footer = unsafe { self.current_footer.as_ref() };

        let ptr = current_footer.ptr.get().as_ptr();
        let end = self.current_footer.as_ptr() as *mut u8;
        debug_assert!(ptr <= end);
        let capacity = end as usize - ptr as usize;

        if capacity < Self::ELEMENT_SIZE {
            return None;
        }

        let new_ptr = ptr.wrapping_byte_add(Self::ELEMENT_SIZE);

        debug_assert!(
            (new_ptr as usize).is_multiple_of(Self::ELEMENT_ALIGN),
            "new bump pointer {new_ptr:#p} should be aligned to the element alignment {:#x}",
            Self::ELEMENT_ALIGN
        );

        let new_ptr = unsafe { NonNull::new_unchecked(new_ptr) };
        current_footer.ptr.set(new_ptr);

        let ptr = unsafe { NonNull::new_unchecked(ptr) };
        Some(ptr.cast())
    }

    // Should be run only if the current chunk is full
    unsafe fn alloc_element_slow(&mut self) -> NonNull<T> {
        unsafe {
            let current_footer = self.current_footer.as_ref();

            debug_assert!(current_footer.remains() < Self::ELEMENT_SIZE);

            if current_footer.is_dead() {
                // this is initial state without allocated chunks at all
                debug_assert!(current_footer.is_dead());
                debug_assert!(current_footer.prev.get().as_ref().is_dead());
                debug_assert!(current_footer.next.get().as_ref().is_dead());

                let new_footer_ptr = self.alloc_chunk(Self::CHUNK_FIRST_SIZE);
                self.current_footer = new_footer_ptr;
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
                    new_footer.prev.set(self.current_footer);

                    self.current_footer = new_footer_ptr;
                } else {
                    // there is a next empty chunk, so make it the current chunk
                    debug_assert!(next_footer.occupied() < Self::ELEMENT_SIZE);
                    self.current_footer = next_footer_ptr;
                }
            }

            self.alloc_element_fast().unwrap_unchecked()
        }
    }

    unsafe fn alloc_chunk(&mut self, chunk_size: usize) -> NonNull<ChunkFooter> {
        debug_assert!((chunk_size + ALLOC_OVERHEAD).is_power_of_two());
        debug_assert!(chunk_size <= Self::CHUNK_MAX_SIZE);

        let mut new_chunk_size = chunk_size;
        let new_chunk_align = Self::CHUNK_ALIGN;

        let (new_chunk_ptr, new_chunk_layout) = loop {
            // checks for `Layout::from_size_align_unchecked`
            debug_assert!(new_chunk_align != 0);
            debug_assert!(new_chunk_align.is_power_of_two());
            debug_assert!((new_chunk_size + ALLOC_OVERHEAD).is_power_of_two());
            debug_assert!(new_chunk_size <= isize::MAX as usize);

            let new_chunk_layout =
                unsafe { Layout::from_size_align_unchecked(new_chunk_size, new_chunk_align) };

            let new_chunk_ptr = unsafe { alloc(new_chunk_layout) };
            if !new_chunk_ptr.is_null() {
                break (new_chunk_ptr, new_chunk_layout);
            }

            new_chunk_size = ((new_chunk_size + ALLOC_OVERHEAD) >> 1) - ALLOC_OVERHEAD;
            if new_chunk_size < Self::CHUNK_MIN_SIZE {
                handle_alloc_error(new_chunk_layout);
            }
        };

        let new_start = new_chunk_ptr;
        let new_end = new_start.wrapping_byte_add(new_chunk_layout.size());
        let new_footer_start = new_end.wrapping_byte_sub(Self::FOOTER_SIZE);
        let new_footer_start = util::round_mut_ptr_down_to(new_footer_start, Self::FOOTER_ALIGN);

        debug_assert!(new_start < new_footer_start);
        debug_assert!(new_footer_start < new_end);

        let new_ptr = util::round_mut_ptr_up_to(new_start, Self::ELEMENT_ALIGN);
        debug_assert!((new_ptr as usize).is_multiple_of(Self::ELEMENT_ALIGN));

        let new_chunk_cap_in_bytes = new_footer_start as usize - new_ptr as usize;
        let new_chunk_cap_in_elements = new_chunk_cap_in_bytes as usize / Self::ELEMENT_SIZE;
        self.capacity += new_chunk_cap_in_elements;

        unsafe {
            let new_footer_ptr = new_footer_start as *mut ChunkFooter;

            util::write_with(new_footer_ptr, || ChunkFooter {
                data: NonNull::new_unchecked(new_start),
                ptr: Cell::new(NonNull::new_unchecked(new_ptr)),
                layout: new_chunk_layout,
                prev: Cell::new(DEAD_CHUNK.get()),
                next: Cell::new(DEAD_CHUNK.get()),
            });

            NonNull::new_unchecked(new_footer_ptr)
        }
    }

    unsafe fn dealloc_element(&mut self) -> Option<NonNull<T>> {
        unsafe {
            if let Some(ptr) = self.dealloc_element_fast() {
                Some(ptr)
            } else {
                self.dealloc_element_slow()
            }
        }
    }

    unsafe fn dealloc_element_fast(&mut self) -> Option<NonNull<T>> {
        let current_footer_ptr = self.current_footer;
        let current_footer = unsafe { current_footer_ptr.as_ref() };

        let start = current_footer.data.as_ptr();
        let ptr = current_footer.ptr.get().as_ptr();
        debug_assert!(start <= ptr);
        let capacity = ptr as usize - start as usize;

        if capacity < Self::ELEMENT_SIZE {
            return None;
        }

        let new_ptr = ptr.wrapping_byte_sub(Self::ELEMENT_SIZE);

        debug_assert!(
            start <= new_ptr,
            "new bump pointer {ptr:#p} should be less than or equal to end {start:#p}"
        );
        debug_assert!(
            (new_ptr as usize).is_multiple_of(Self::ELEMENT_ALIGN),
            "new bump pointer {new_ptr:#p} should be aligned to the element alignment {:#x}",
            Self::ELEMENT_ALIGN
        );

        let new_ptr = unsafe { NonNull::new_unchecked(new_ptr) };
        current_footer.ptr.set(new_ptr);

        Some(new_ptr.cast())
    }

    unsafe fn dealloc_element_slow(&mut self) -> Option<NonNull<T>> {
        unsafe {
            let current_footer_ptr = self.current_footer;
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

            debug_assert!(current_footer.occupied() < Self::ELEMENT_SIZE);
            debug_assert!(next_footer.occupied() < Self::ELEMENT_SIZE);

            if !next_footer.is_dead() {
                if current_footer.layout.size() < next_footer.layout.size() {
                    debug_assert!(next_footer.next.get().as_ref().is_dead());

                    self.current_footer = next_footer_ptr;
                    self.current_footer.as_ref().prev.set(prev_footer_ptr);

                    self.dealloc_chunk(current_footer_ptr);
                } else {
                    self.dealloc_chunk(next_footer_ptr);
                }
                self.current_footer.as_ref().next.set(DEAD_CHUNK.get());
            }

            if prev_footer.is_dead() {
                None
            } else {
                // check if prev_footer is full
                debug_assert!(prev_footer.remains() < Self::ELEMENT_SIZE);

                prev_footer.next.set(self.current_footer);
                self.current_footer = prev_footer_ptr;

                self.dealloc_element_fast()
            }
        }
    }

    unsafe fn dealloc_chunk(&mut self, mut footer_ptr: NonNull<ChunkFooter>) {
        unsafe {
            let footer = footer_ptr.as_mut();
            let chunk_capacity = footer.capacity() / Self::ELEMENT_SIZE;
            debug_assert!(chunk_capacity <= self.capacity());
            self.capacity -= chunk_capacity;
            debug_assert!(self.len() <= self.capacity());
            dealloc(footer.data.as_ptr(), footer.layout);
        }
    }
}

/// Collection of static tests for inner constants of Stack. They are enabled
/// only for some platforms, where I could test them. Look inside to see which
/// ones exactly.
mod stest;

/// Unit tests.
#[cfg(test)]
mod utest;
