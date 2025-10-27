#![no_std]

pub(crate) mod util;

extern crate alloc;

use alloc::alloc::{Layout, alloc, dealloc, handle_alloc_error};
use core::cell::Cell;
use core::marker::PhantomData;
use core::mem;
use core::ptr::{self, NonNull};

#[derive(Debug)]
pub struct Stack<T, const MIN_ALIGN: usize = 1> {
    /// The current chunk we are bump allocating within.
    ///
    /// Its `next` link can point to the none chunk, or to the cached chunk.
    ///
    /// Its `prev` link can point to the none chunk or to the earlier allocated
    /// chunk.
    current_footer: NonNull<ChunkFooter>,

    /// The capacity of the stack in elements.
    capacity: usize,

    /// The number of elements currently in the stack.
    length: usize,

    _phantom: PhantomData<T>,
}

// Public API
impl<T, const MIN_ALIGN: usize> Stack<T, MIN_ALIGN> {
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
            current_footer: NONE_CHUNK.get(),
            capacity: 0,
            length: 0,
            _phantom: PhantomData,
        }
    }

    /// Returns the total number of elements the stack can hold without new
    /// allocating.
    #[inline]
    pub const fn capacity(&self) -> usize {
        self.capacity
    }

    /// Returns the number of elements in the vector, also referred to as its ‘length’.
    #[inline]
    pub const fn len(&self) -> usize {
        self.length
    }

    /// Returns `true` if the stack contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use bump_stack::Stack;
    ///
    /// let mut s = Stack::<i32>::new();
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
        if let Some(element) = unsafe { self.dealloc_element() } {
            self.length -= 1;
            Some(element)
        } else {
            None
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

impl<T, const MIN_ALIGN: usize> core::ops::Drop for Stack<T, MIN_ALIGN> {
    fn drop(&mut self) {
        while let Some(item) = self.pop() {
            drop(item);
        }
        unsafe {
            let current_footer_ref = self.current_footer.as_ref();
            if !current_footer_ref.is_none() {
                debug_assert!(current_footer_ref.next.get().as_ref().is_none());
                debug_assert!(current_footer_ref.prev.get().as_ref().is_none());
                self.dealloc_chunk(current_footer_ref);
            }
        }
    }
}

#[derive(Debug)]
struct ChunkFooter {
    // Pointer to the start of this chunk allocation. This footer is always at
    // the end of the chunk. So memory available for allocation is
    // `self.data..=self`.
    data: NonNull<u8>,

    // Bump allocation finger that is always in the range `self.data..=self`.
    ptr: Cell<NonNull<u8>>,

    // The layout of this chunk's allocation.
    layout: Layout,

    // Link to the previous chunk.
    //
    // Note that the last node in the `prev` linked list is the none chunk,
    // whose `prev` link points to itself.
    prev: Cell<NonNull<ChunkFooter>>,

    // Link to the next chunk.
    //
    // Note that the last node in the `next` linked list is the none chunk,
    // whose `next` link points to itself.
    next: Cell<NonNull<ChunkFooter>>,
}

#[repr(transparent)]
struct NoneChunkFooter(ChunkFooter);

unsafe impl Sync for NoneChunkFooter {}

impl NoneChunkFooter {
    const fn get(&'static self) -> NonNull<ChunkFooter> {
        NonNull::new(&self.0 as *const ChunkFooter as *mut ChunkFooter).unwrap()
    }
}

// Empty chunk that contains only its footer.
static NONE_CHUNK: NoneChunkFooter = NoneChunkFooter(unsafe {
    ChunkFooter {
        data: NonNull::new_unchecked(&NONE_CHUNK as *const NoneChunkFooter as *mut u8),
        ptr: Cell::new(NonNull::new_unchecked(
            &NONE_CHUNK as *const NoneChunkFooter as *mut u8,
        )),
        layout: Layout::new::<ChunkFooter>(),
        prev: Cell::new(NonNull::new_unchecked(
            &NONE_CHUNK as *const NoneChunkFooter as *mut ChunkFooter,
        )),
        next: Cell::new(NonNull::new_unchecked(
            &NONE_CHUNK as *const NoneChunkFooter as *mut ChunkFooter,
        )),
    }
});

impl ChunkFooter {
    /// This is the `NONE_CHUNK` chunk.
    fn is_none(&self) -> bool {
        ptr::eq(self, &NONE_CHUNK.0)
    }

    /// Amount of unoccupied bytes in the chunk.
    fn remains(&self) -> usize {
        let start = self.data.as_ptr() as usize;
        let ptr = self.ptr.get().as_ptr() as usize;
        debug_assert!(start <= ptr);
        ptr - start
    }

    /// The chunk is empty.
    fn is_empty(&self) -> bool {
        let ptr = self.ptr.get().as_ptr() as usize;
        let end = self as *const Self as usize;
        debug_assert!(ptr <= end);
        ptr == end
    }

    /// The capacity of the chunk in bytes.
    fn capacity(&self) -> usize {
        let end = self as *const Self as usize;
        let start = self.data.as_ptr() as usize;
        debug_assert!(start < end);
        end - start
    }
}

// Constants
impl<T, const MIN_ALIGN: usize> Stack<T, MIN_ALIGN> {
    /// Element alignment takes into account the `MIN_ALIGN`. It takes the maximum
    /// between `MIN_ALIGN` and `T`'s alignment.
    const ELEMENT_ALIGN: usize = {
        assert!(MIN_ALIGN.is_power_of_two());
        util::max(mem::align_of::<T>(), MIN_ALIGN)
    };

    /// `ELEMENT_SIZE` is not always equal to `T`'s size. This is actually the
    /// size of memory space required to store an `T` element with required
    /// alignment.
    const ELEMENT_SIZE: usize = mem::size_of::<T>()
        .checked_next_multiple_of(Self::ELEMENT_ALIGN)
        .unwrap();

    /// It is expected that the footer alignment is equal or greater than the
    /// element alignment, because the footer address is expected to be a marker
    /// of the `(last + 1)`-th element.
    const FOOTER_ALIGN: usize =
        util::max(Layout::new::<ChunkFooter>().align(), Self::ELEMENT_ALIGN);

    const FOOTER_SIZE: usize = mem::size_of::<ChunkFooter>();

    /// Chunk alignment is the same as element alignment.
    const CHUNK_ALIGN: usize = util::max(Self::ELEMENT_ALIGN, 8);

    /// Chunk size enough for at least one element.
    const CHUNK_MIN_SIZE: usize = Self::chunk_size_for(1);

    /// Chunk size for the first chunk if capacity is not specified with
    /// [`Stack::with_capacity`].
    const CHUNK_FIRST_SIZE: usize = util::max(Self::chunk_size_for(8), 0x200);

    /// Maximal possible chunk size. Is equal to 4 GiB, if address space is not
    /// limited. Otherwise, it is equal to (address space size / 8).
    const CHUNK_MAX_SIZE: usize = {
        let part_of_entire_memory = util::round_down_to_pow2(isize::MAX as usize >> 2);
        let common_sensible_in_2025 = 4 << 30; // 4 GiB
        util::min(part_of_entire_memory, common_sensible_in_2025)
    };

    /// Calculate chunk size big enough for the given number of elements. The
    /// chunk is a power of two.
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

        chunk_size = chunk_size.next_multiple_of(Self::FOOTER_ALIGN);
        chunk_size += Self::FOOTER_SIZE;

        chunk_size.next_power_of_two()
    }
}

// Private API
impl<T, const MIN_ALIGN: usize> Stack<T, MIN_ALIGN> {
    unsafe fn alloc_element(&mut self) -> NonNull<T> {
        if let Some(ptr) = self.try_alloc_element_fast() {
            ptr
        } else {
            unsafe { self.alloc_element_slow() }
        }
    }

    fn try_alloc_element_fast(&self) -> Option<NonNull<T>> {
        let current_footer = unsafe { self.current_footer.as_ref() };

        let start = current_footer.data.as_ptr();
        let ptr = current_footer.ptr.get().as_ptr();
        let capacity = ptr as usize - start as usize;

        if capacity < Self::ELEMENT_SIZE {
            return None;
        }

        let new_ptr = ptr.wrapping_byte_sub(Self::ELEMENT_SIZE);

        debug_assert!(
            (new_ptr as usize).is_multiple_of(Self::ELEMENT_ALIGN),
            "new bump pointer {new_ptr:#p} should be aligned to the element alignment {:#x}",
            Self::ELEMENT_ALIGN
        );

        let new_ptr = unsafe { NonNull::new_unchecked(new_ptr) };
        current_footer.ptr.set(new_ptr);

        Some(new_ptr.cast())
    }

    // Should be run only if the current chunk is full
    unsafe fn alloc_element_slow(&mut self) -> NonNull<T> {
        unsafe {
            let current_footer_ptr = self.current_footer;
            let current_footer_ref = current_footer_ptr.as_ref();

            debug_assert!(current_footer_ref.remains() < Self::ELEMENT_SIZE);

            if current_footer_ref.is_none() {
                // this is initial stated without allocated chunks at all
                let new_footer_ptr = self.alloc_chunk(Self::CHUNK_FIRST_SIZE);
                self.current_footer = new_footer_ptr;
            } else {
                // at least the current chunk is not none

                let next_footer_ptr = current_footer_ref.next.get();
                let next_footer_ref = next_footer_ptr.as_ref();

                if next_footer_ref.is_none() {
                    // the current chunk is single, so create a new one, and
                    // make it the current chunk.

                    let current_chunk_size = current_footer_ref.layout.size();
                    let new_chunk_size = if current_chunk_size == Self::CHUNK_MAX_SIZE {
                        Self::CHUNK_MAX_SIZE
                    } else {
                        current_chunk_size << 1
                    };

                    let new_footer_ptr = self.alloc_chunk(new_chunk_size);
                    let new_footer_ref = new_footer_ptr.as_ref();

                    current_footer_ref.next.set(new_footer_ptr);
                    new_footer_ref.prev.set(self.current_footer);

                    self.current_footer = new_footer_ptr;
                } else {
                    // there is a next empty chunk, so make it the current chunk
                    debug_assert!(next_footer_ref.is_empty());
                    self.current_footer = next_footer_ptr;
                }
            }

            self.try_alloc_element_fast().unwrap_unchecked()
        }
    }

    unsafe fn alloc_chunk(&mut self, chunk_size: usize) -> NonNull<ChunkFooter> {
        debug_assert!(chunk_size.is_power_of_two());
        debug_assert!(chunk_size <= Self::CHUNK_MAX_SIZE);

        let mut new_chunk_size = chunk_size;
        let new_chunk_align = Self::CHUNK_ALIGN;

        let (new_chunk_ptr, new_chunk_layout) = loop {
            // checks for `Layout::from_size_align_unchecked`
            debug_assert!(
                new_chunk_align != 0,
                "chunk alignment {new_chunk_align:#x} should not be zero"
            );
            debug_assert!(
                new_chunk_align.is_power_of_two(),
                "chunk alignment {new_chunk_align:#x} should be a power of two"
            );
            debug_assert!(
                new_chunk_size.is_power_of_two(),
                "chunk size {new_chunk_size:#x} should be a power of two"
            );

            let new_chunk_layout =
                unsafe { Layout::from_size_align_unchecked(new_chunk_size, new_chunk_align) };

            let new_chunk_ptr = unsafe { alloc(new_chunk_layout) };
            if !new_chunk_ptr.is_null() {
                break (new_chunk_ptr, new_chunk_layout);
            }

            new_chunk_size >>= 1;
            if new_chunk_size < Self::CHUNK_MIN_SIZE {
                handle_alloc_error(new_chunk_layout);
            }
        };

        let new_start = new_chunk_ptr as usize;
        let new_end = new_start + new_chunk_layout.size();
        let new_footer_start = util::round_down_to(new_end - Self::FOOTER_SIZE, Self::FOOTER_ALIGN);

        debug_assert!(new_footer_start.is_multiple_of(Self::ELEMENT_ALIGN));
        let new_ptr = new_footer_start;

        let new_chunk_capacity = (new_ptr - new_start) / Self::ELEMENT_SIZE;
        self.capacity += new_chunk_capacity;

        unsafe {
            let new_footer_ptr = ptr::with_exposed_provenance_mut::<ChunkFooter>(new_footer_start);
            let new_start_ptr = ptr::with_exposed_provenance_mut::<u8>(new_start);
            let new_ptr = ptr::with_exposed_provenance_mut::<u8>(new_ptr);

            util::write_with(new_footer_ptr, || ChunkFooter {
                data: NonNull::new_unchecked(new_start_ptr),
                ptr: Cell::new(NonNull::new_unchecked(new_ptr)),
                layout: new_chunk_layout,
                prev: Cell::new(NONE_CHUNK.get()),
                next: Cell::new(NONE_CHUNK.get()),
            });

            NonNull::new_unchecked(new_footer_ptr)
        }
    }

    unsafe fn dealloc_element(&mut self) -> Option<T> {
        unsafe {
            if let Some(ptr) = self.try_dealloc_element_fast() {
                Some(ptr::read(ptr))
            } else {
                self.try_dealloc_element_slow().map(|ptr| ptr::read(ptr))
            }
        }
    }

    unsafe fn try_dealloc_element_fast(&mut self) -> Option<*const T> {
        let current_footer_ptr = self.current_footer;
        let current_footer_ref = unsafe { current_footer_ptr.as_ref() };

        let ptr = current_footer_ref.ptr.get().as_ptr() as *mut T;
        let end = current_footer_ptr.as_ptr() as *mut T;

        if ptr == end {
            return None;
        }

        let new_ptr = ptr.wrapping_byte_add(Self::ELEMENT_SIZE);

        debug_assert!(
            ptr <= end,
            "new bump pointer {ptr:#p} should be less than or equal to end {end:#p}"
        );
        debug_assert!(
            (new_ptr as usize).is_multiple_of(Self::ELEMENT_ALIGN),
            "new bump pointer {new_ptr:#p} should be aligned to the element alignment {:#x}",
            Self::ELEMENT_ALIGN
        );

        let new_ptr = unsafe { NonNull::new_unchecked(new_ptr as *mut u8) };
        current_footer_ref.ptr.set(new_ptr);

        Some(ptr as *const T)
    }

    unsafe fn try_dealloc_element_slow(&mut self) -> Option<*const T> {
        unsafe {
            let current_footer_ptr = self.current_footer;
            let current_footer_ref = current_footer_ptr.as_ref();

            let next_footer_ptr = current_footer_ref.next.get();
            let next_footer_ref = next_footer_ptr.as_ref();

            debug_assert!(current_footer_ref.is_empty());
            debug_assert!(next_footer_ref.is_none());

            let prev_footer_ptr = current_footer_ref.prev.get();
            let prev_footer_ref = next_footer_ptr.as_ref();

            if current_footer_ref.is_none() {
                debug_assert!(next_footer_ref.is_none());
                debug_assert!(prev_footer_ref.is_none());
                return None;
            }

            if !next_footer_ref.is_none() {
                let (smaller_ptr, larger_ptr) =
                    if current_footer_ref.layout.size() < next_footer_ref.layout.size() {
                        (current_footer_ptr, next_footer_ptr)
                    } else {
                        (next_footer_ptr, current_footer_ptr)
                    };

                self.current_footer = larger_ptr;
                self.current_footer.as_ref().prev.set(prev_footer_ptr);
                self.current_footer.as_ref().next.set(NONE_CHUNK.get());

                self.dealloc_chunk(smaller_ptr.as_ref());
            }

            if prev_footer_ref.is_none() {
                None
            } else {
                debug_assert!(prev_footer_ref.remains() < Self::ELEMENT_SIZE);

                prev_footer_ref.next.set(self.current_footer);
                self.current_footer = prev_footer_ptr;

                self.try_dealloc_element_fast()
            }
        }
    }

    unsafe fn dealloc_chunk(&mut self, footer: &ChunkFooter) {
        unsafe {
            let chunk_capacity = footer.capacity() / Self::ELEMENT_SIZE;
            debug_assert!(chunk_capacity <= self.capacity());
            self.capacity -= chunk_capacity;
            debug_assert!(self.len() <= self.capacity());
            dealloc(footer.data.as_ptr(), footer.layout);
        }
    }
}

mod stest; // static checks
mod utest; // unit tests
