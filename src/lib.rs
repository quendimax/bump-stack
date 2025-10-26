#![no_std]

pub(crate) mod util;

extern crate alloc;

use alloc::alloc::{Layout, alloc, handle_alloc_error};
use core::cell::Cell;
use core::marker::PhantomData;
use core::mem;
use core::ptr::NonNull;

#[derive(Debug)]
pub struct Stack<T, const MIN_ALIGN: usize = 1> {
    // The current chunk we are bump allocating within.
    current_footer: NonNull<ChunkFooter>,

    /// The capacity of the stack in elements.
    capacity: usize,

    /// The number of elements currently in the stack.
    length: usize,

    _phantom: PhantomData<T>,
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
    // Note that the last node in the `prev` linked list is the canonical empty
    // chunk, whose `prev` link points to itself.
    prev: Cell<NonNull<ChunkFooter>>,

    // Link to the next chunk.
    //
    // Note that the first node in the `next` linked list is the canonical empty
    // chunk, whose `next` link points to itself.
    next: Cell<NonNull<ChunkFooter>>,
}

#[repr(transparent)]
struct EmptyChunkFooter(ChunkFooter);

unsafe impl Sync for EmptyChunkFooter {}

impl EmptyChunkFooter {
    fn get(&self) -> NonNull<ChunkFooter> {
        NonNull::from(&self.0)
    }
}

// Empty chunk that contains only its footer.
static EMPTY_CHUNK: EmptyChunkFooter = EmptyChunkFooter(unsafe {
    ChunkFooter {
        data: NonNull::new_unchecked(&EMPTY_CHUNK as *const EmptyChunkFooter as *mut u8),
        ptr: Cell::new(NonNull::new_unchecked(
            &EMPTY_CHUNK as *const EmptyChunkFooter as *mut u8,
        )),
        layout: Layout::new::<ChunkFooter>(),
        prev: Cell::new(NonNull::new_unchecked(
            &EMPTY_CHUNK as *const EmptyChunkFooter as *mut ChunkFooter,
        )),
        next: Cell::new(NonNull::new_unchecked(
            &EMPTY_CHUNK as *const EmptyChunkFooter as *mut ChunkFooter,
        )),
    }
});

impl ChunkFooter {
    fn is_empty(&self) -> bool {
        core::ptr::eq(self, &EMPTY_CHUNK.0)
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
    const fn chunk_size_for(elements_count: usize) -> usize {
        let mut chunk_size = elements_count * Self::ELEMENT_SIZE;
        assert!(chunk_size.is_multiple_of(Self::ELEMENT_ALIGN));

        chunk_size = chunk_size.next_multiple_of(Self::FOOTER_ALIGN);
        chunk_size += Self::FOOTER_SIZE;

        // for a case (is it possible?) if the alloc returns unaligned pointer.
        chunk_size += util::max(Self::FOOTER_ALIGN, Self::ELEMENT_ALIGN) - 1;
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
            None
        } else {
            let new_ptr = ptr.wrapping_byte_sub(Self::ELEMENT_SIZE);

            debug_assert!(
                (new_ptr as usize).is_multiple_of(Self::ELEMENT_ALIGN),
                "new bump pointer {new_ptr:#p} should be aligned to the element alignment {:#x}",
                Self::ELEMENT_ALIGN
            );

            Some(unsafe { NonNull::new_unchecked(new_ptr as *mut T) })
        }
    }

    unsafe fn alloc_element_slow(&mut self) -> NonNull<T> {
        unsafe {
            let current_footer_ptr = self.current_footer;
            let current_footer_ref = current_footer_ptr.as_ref();

            let next_footer_ptr = current_footer_ref.next.get();
            let next_footer_ref = next_footer_ptr.as_ref();

            if current_footer_ref.is_empty() {
                let new_footer_ptr = self.alloc_chunk(Self::CHUNK_FIRST_SIZE);
                self.current_footer = new_footer_ptr;
            } else if next_footer_ref.is_empty() {
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
                self.current_footer = next_footer_ptr;
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
        let new_ptr = util::round_down_to(new_footer_start, Self::ELEMENT_ALIGN);

        let new_chunk_capacity = (new_ptr - new_start) / Self::ELEMENT_SIZE;
        self.capacity += new_chunk_capacity;

        unsafe {
            let new_footer_ptr = NonNull::new_unchecked(new_footer_start as *mut ChunkFooter);

            util::write_with(new_footer_ptr.as_ptr(), || ChunkFooter {
                data: NonNull::new_unchecked(new_start as *mut u8),
                ptr: Cell::new(NonNull::new_unchecked(new_ptr as *mut u8)),
                layout: new_chunk_layout,
                prev: Cell::new(EMPTY_CHUNK.get()),
                next: Cell::new(EMPTY_CHUNK.get()),
            });

            new_footer_ptr
        }
    }
}

// Public API
impl<T, const MIN_ALIGN: usize> Stack<T, MIN_ALIGN> {
    pub fn new() -> Self {
        Self {
            current_footer: EMPTY_CHUNK.get(),
            capacity: 0,
            length: 0,
            _phantom: PhantomData,
        }
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.length
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.length == 0
    }

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
}
impl<T> core::default::Default for Stack<T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

mod stest; // static checks
mod utest; // unit tests
