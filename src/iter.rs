use crate::{ChunkFooter, Stack};
use core::iter::Iterator;
use core::ptr::NonNull;

pub struct Iter<'a, T> {
    _stack: &'a Stack<T>,

    /// The chunk's footer where the iterating is running on.
    current_footer: NonNull<ChunkFooter>,

    /// # For non-ZST elements
    ///
    /// The address of the next element that should be returned by this
    /// iterator.
    ///
    /// # For ZST elements
    ///
    /// The index of the next element that should be returned by this iterator.
    ptr_or_idx: *const T,

    /// # For non-ZST elements
    ///
    /// The address of element after the last one that the iterator should run
    /// over, i.e.
    ///
    /// # For ZST elements
    ///
    /// The number of elements that the iterator should run over.
    end_or_len: *const T,
}

impl<'a, T> Iter<'a, T> {
    pub(crate) fn new(stack: &'a Stack<T>) -> Self {
        let current_footer = unsafe { stack.current_footer.get().as_ref() };
        if const { Stack::<T>::ELEMENT_IS_ZST } {
            Self {
                _stack: stack,
                current_footer: current_footer.get(),
                ptr_or_idx: core::ptr::without_provenance(0),
                end_or_len: core::ptr::without_provenance(stack.len()),
            }
        } else {
            let ptr = unsafe { stack.first_footer.get().as_ref().data.cast().as_ptr() };
            let end = current_footer.ptr.get().cast().as_ptr();
            Self {
                _stack: stack,
                current_footer: stack.first_footer.get(),
                ptr_or_idx: ptr,
                end_or_len: end,
            }
        }
    }
}

impl<'a, T> Iter<'a, T> {
    #[inline(always)]
    unsafe fn next_element_fast(&mut self) -> Option<NonNull<T>> {
        unsafe {
            let current_footer = self.current_footer.as_ref();
            let chunk_ptr = current_footer.ptr.get().cast().as_ptr();

            if self.ptr_or_idx != chunk_ptr {
                let ptr = self.ptr_or_idx;
                self.ptr_or_idx = ptr.byte_add(Stack::<T>::ELEMENT_SIZE);
                Some(NonNull::new_unchecked(ptr as *mut T))
            } else {
                None
            }
        }
    }

    unsafe fn next_element_slow(&mut self) -> Option<NonNull<T>> {
        unsafe {
            let current_footer = self.current_footer.as_ref();
            self.current_footer = current_footer.next.get();

            let current_footer = self.current_footer.as_ref();
            self.ptr_or_idx = current_footer.data.cast().as_ptr();

            self.next_element_fast()
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if const { Stack::<T>::ELEMENT_IS_ZST } {
            if self.ptr_or_idx < self.end_or_len {
                unsafe {
                    self.ptr_or_idx = self.ptr_or_idx.wrapping_byte_add(1);
                    Some(self.current_footer.cast().as_ref())
                }
            } else {
                None
            }
        } else {
            if self.ptr_or_idx == self.end_or_len {
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
        if const { Stack::<T>::ELEMENT_IS_ZST } {
            let remains = self.end_or_len as usize - self.ptr_or_idx as usize;
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
        if const { Stack::<T>::ELEMENT_IS_ZST } {
            self.end_or_len as usize - self.ptr_or_idx as usize
        } else {
            self.fold(0, |count, _| count + 1)
        }
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        let m = n + 1;
        let mut need = m * Stack::<T>::ELEMENT_SIZE;
        if const { Stack::<T>::ELEMENT_IS_ZST } {
            let index = self.ptr_or_idx as usize;
            let length = self.end_or_len as usize;
            if length - index > n {
                unsafe {
                    self.ptr_or_idx = self.ptr_or_idx.wrapping_byte_add(m);
                    Some(self.current_footer.cast().as_ref())
                }
            } else {
                self.ptr_or_idx = self.end_or_len;
                None
            }
        } else {
            loop {
                let current_footer = unsafe { self.current_footer.as_ref() };
                let current_start = current_footer.data.as_ptr() as *const T;
                let current_end = current_footer.ptr.get().as_ptr() as *const T;
                let ptr = self.ptr_or_idx;
                let end = self.end_or_len;

                if current_start <= end && end <= current_end {
                    let size = end as usize - ptr as usize;
                    if need <= size {
                        let new_ptr = ptr.wrapping_byte_add(need);
                        let ptr = ptr.wrapping_byte_add(need - Stack::<T>::ELEMENT_SIZE);
                        self.ptr_or_idx = new_ptr;
                        break Some(unsafe { &*ptr });
                    } else {
                        self.ptr_or_idx = end;
                        break None;
                    }
                } else {
                    debug_assert!(current_start <= ptr && ptr <= current_end);
                    let size = current_end as usize - ptr as usize;
                    if need <= size {
                        let new_ptr = ptr.wrapping_byte_add(need);
                        let ptr = ptr.wrapping_byte_add(need - Stack::<T>::ELEMENT_SIZE);
                        self.ptr_or_idx = new_ptr;
                        break Some(unsafe { &*ptr });
                    } else {
                        need -= size;
                        self.current_footer = current_footer.next.get();
                        self.ptr_or_idx =
                            unsafe { self.current_footer.as_ref().data.cast().as_ptr() };
                    }
                }
            }
        }
    }
}
