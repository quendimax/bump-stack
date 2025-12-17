use crate::{ChunkFooter, Stack};
use core::iter::{DoubleEndedIterator, Iterator};
use core::marker::PhantomData;
use core::ptr::NonNull;

pub struct Iter<'a, T> {
    /// The chunk's footer where `first_or_idx` besides within.
    first_footer: NonNull<ChunkFooter>,

    /// The chunk's footer where `last_or_len` besides within.
    last_footer: NonNull<ChunkFooter>,

    /// # For non-ZST elements
    ///
    /// The address of element that was pushed first, and should be returned by
    /// this iterator last.
    ///
    /// # For ZST elements
    ///
    /// The index of the next element that should be returned by this iterator.
    first_or_idx: *const T,

    /// # For non-ZST elements
    ///
    /// The address of element that was pushed last, and should be returned by
    /// this iterator first.
    ///
    /// # For ZST elements
    ///
    /// The number of elements that the iterator should run over.
    last_or_len: *const T,

    _phantom: PhantomData<&'a T>,
}

impl<'a, T> Iter<'a, T> {
    const ELEMENT_SIZE: usize = Stack::<T>::ELEMENT_SIZE;
    const ELEMENT_IS_ZST: bool = Stack::<T>::ELEMENT_IS_ZST;
    const FOOTER_IS_END: bool = Stack::<T>::FOOTER_IS_END;

    pub(crate) fn new(stack: &'a Stack<T>) -> Self {
        let current_footer = unsafe { stack.current_footer.get().as_ref() };
        if const { Self::ELEMENT_IS_ZST } {
            Self {
                first_footer: current_footer.get(),
                last_footer: current_footer.get(),
                first_or_idx: core::ptr::without_provenance(0),
                last_or_len: core::ptr::without_provenance(stack.len()),
                _phantom: PhantomData,
            }
        } else {
            let first_ptr = unsafe { eval_end_ptr(stack.first_footer.get()) };
            let last_ptr = current_footer.ptr.get().cast().as_ptr();
            Self {
                first_footer: stack.first_footer.get(),
                last_footer: current_footer.get(),
                first_or_idx: first_ptr,
                last_or_len: last_ptr,
                _phantom: PhantomData,
            }
        }
    }
}

impl<'a, T> Iter<'a, T> {
    #[inline(always)]
    unsafe fn next_element_fast(&mut self) -> Option<NonNull<T>> {
        unsafe {
            let ptr = self.last_or_len as usize;
            let end = self.last_footer.as_ptr() as usize;
            debug_assert!(ptr <= end);

            let chunk_is_empty = if const { Self::FOOTER_IS_END } {
                ptr == end
            } else {
                end - ptr < Self::ELEMENT_SIZE
            };

            if !chunk_is_empty {
                let ptr = self.last_or_len;
                self.last_or_len = ptr.wrapping_add(1);
                Some(NonNull::new_unchecked(ptr as *mut T))
            } else {
                None
            }
        }
    }

    unsafe fn next_element_slow(&mut self) -> Option<NonNull<T>> {
        unsafe {
            let last_footer = self.last_footer.as_ref();
            self.last_footer = last_footer.prev.get();

            let new_last_footer = self.last_footer.as_ref();
            self.last_or_len = new_last_footer.ptr.get().cast().as_ptr();

            if self.first_or_idx == self.last_or_len {
                return None;
            }

            self.next_element_fast()
        }
    }

    #[inline(always)]
    unsafe fn prev_element_fast(&mut self) -> Option<NonNull<T>> {
        unsafe {
            let first_footer = self.first_footer.as_ref();
            let chunk_start = first_footer.data.cast().as_ptr() as *const T;
            debug_assert!(chunk_start <= self.first_or_idx);

            let ptr = self.first_or_idx;
            if ptr != chunk_start {
                self.first_or_idx = ptr.wrapping_sub(1);
                debug_assert!(chunk_start <= self.first_or_idx);
                Some(NonNull::new_unchecked(self.first_or_idx as *mut T))
            } else {
                None
            }
        }
    }

    unsafe fn prev_element_slow(&mut self) -> Option<NonNull<T>> {
        unsafe {
            let first_footer = self.first_footer.as_ref();
            self.first_footer = first_footer.next.get();
            self.first_or_idx = eval_end_ptr(self.first_footer);

            if self.first_or_idx == self.last_or_len {
                return None;
            }

            self.prev_element_fast()
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if const { Self::ELEMENT_IS_ZST } {
            if self.first_or_idx < self.last_or_len {
                unsafe {
                    self.first_or_idx = self.first_or_idx.wrapping_byte_add(1);
                    Some(self.first_footer.cast().as_ref())
                }
            } else {
                None
            }
        } else {
            if self.first_or_idx == self.last_or_len {
                return None;
            }
            unsafe {
                if let Some(elem_ptr) = self.next_element_fast() {
                    Some(elem_ptr.as_ref())
                } else {
                    self.next_element_slow().map(|ptr| ptr.as_ref())
                }
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if const { Self::ELEMENT_IS_ZST } {
            let remains = self.last_or_len as usize - self.first_or_idx as usize;
            (remains, Some(remains))
        } else {
            (0, None)
        }
    }

    #[inline]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        if const { Self::ELEMENT_IS_ZST } {
            self.last_or_len as usize - self.first_or_idx as usize
        } else {
            let mut count = 0;
            let buffer_end = self.last_footer.as_ptr() as usize;
            let ptr = self.last_or_len as usize;
            count += (buffer_end - ptr) / Self::ELEMENT_SIZE;

            let mut footer = unsafe { self.last_footer.as_ref().prev.get().as_ref() };
            while !footer.is_dead() {
                let capacity = footer.capacity();
                count += capacity / Self::ELEMENT_SIZE;
                footer = unsafe { footer.prev.get().as_ref() };
            }
            count
        }
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        let m = n + 1;
        let mut need = m * Self::ELEMENT_SIZE;
        if const { Self::ELEMENT_IS_ZST } {
            let index = self.first_or_idx as usize;
            let length = self.last_or_len as usize;
            if length - index > n {
                unsafe {
                    self.first_or_idx = self.first_or_idx.wrapping_byte_add(m);
                    Some(self.first_footer.cast().as_ref())
                }
            } else {
                self.first_or_idx = self.last_or_len;
                None
            }
        } else {
            loop {
                let last_footer = unsafe { self.last_footer.as_ref() };
                let first_ptr = self.first_or_idx;
                let last_ptr = self.last_or_len;

                if self.last_footer == self.first_footer {
                    debug_assert!(last_ptr <= first_ptr);
                    let size = first_ptr as usize - last_ptr as usize;
                    if need <= size {
                        let new_ptr = last_ptr.wrapping_byte_add(need);
                        self.last_or_len = new_ptr;
                        let ptr = last_ptr.wrapping_byte_add(need - Self::ELEMENT_SIZE);
                        break Some(unsafe { &*ptr });
                    } else {
                        self.last_or_len = first_ptr;
                        break None;
                    }
                } else {
                    // can ignore the gap between the buffer and the footer,
                    // because: 0 <= gap < ELEMENT_SIZE
                    let chunk_end = last_footer as *const ChunkFooter as *const T;
                    let size = chunk_end as usize - last_ptr as usize;
                    if need <= size {
                        let new_ptr = last_ptr.wrapping_byte_add(need);
                        self.last_or_len = new_ptr;
                        let ptr = last_ptr.wrapping_byte_add(need - Self::ELEMENT_SIZE);
                        break Some(unsafe { &*ptr });
                    } else {
                        need -= size;
                        self.last_footer = last_footer.prev.get();
                        self.last_or_len =
                            unsafe { self.last_footer.as_ref().data.cast().as_ptr() };
                    }
                }
            }
        }
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if const { Self::ELEMENT_IS_ZST } {
            // it just increments `ptr_or_idx`
            return self.next();
        }
        if self.first_or_idx == self.last_or_len {
            return None;
        }
        unsafe {
            if let Some(elem_ptr) = self.prev_element_fast() {
                Some(elem_ptr.as_ref())
            } else {
                self.prev_element_slow().map(|ptr| ptr.as_ref())
            }
        }
    }
}

unsafe fn eval_end_ptr<T>(footer_ptr: NonNull<ChunkFooter>) -> *mut T {
    if const { Stack::<T>::FOOTER_IS_END } {
        return footer_ptr.cast().as_ptr();
    }

    let footer = unsafe { footer_ptr.as_ref() };
    let footer_addr = footer_ptr.as_ptr();
    let chunk_start = footer.data.as_ptr();
    let chunk_cap_in_bytes = footer_addr as usize - chunk_start as usize;
    let chunk_capacity = chunk_cap_in_bytes / size_of::<T>();

    let buffer_size = chunk_capacity * size_of::<T>();
    let end_ptr = chunk_start.wrapping_byte_add(buffer_size);
    debug_assert!(end_ptr as usize <= footer_addr as usize);

    end_ptr as *mut T
}
