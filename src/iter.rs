use crate::{ChunkFooter, Stack};
use core::iter::{DoubleEndedIterator, Iterator};
use core::marker::PhantomData;
use core::ptr::NonNull;

pub struct Iter<'a, T> {
    /// The chunk's footer where `ptr_or_idx` besides within.
    start_footer: NonNull<ChunkFooter>,

    /// The chunk's footer where `end_or_len` besides within.
    end_footer: NonNull<ChunkFooter>,

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

    _phantom: PhantomData<&'a [T]>,
}

impl<'a, T> Iter<'a, T> {
    pub(crate) fn new(stack: &'a Stack<T>) -> Self {
        let current_footer = unsafe { stack.current_footer.get().as_ref() };
        if const { Stack::<T>::ELEMENT_IS_ZST } {
            Self {
                start_footer: current_footer.get(),
                end_footer: current_footer.get(),
                ptr_or_idx: core::ptr::without_provenance(0),
                end_or_len: core::ptr::without_provenance(stack.len()),
                _phantom: PhantomData,
            }
        } else {
            let ptr = unsafe { stack.first_footer.get().as_ref().data.cast().as_ptr() };
            let end = current_footer.ptr.get().cast().as_ptr();
            Self {
                start_footer: stack.first_footer.get(),
                end_footer: current_footer.get(),
                ptr_or_idx: ptr,
                end_or_len: end,
                _phantom: PhantomData,
            }
        }
    }
}

impl<'a, T> Iter<'a, T> {
    #[inline(always)]
    unsafe fn next_element_fast(&mut self) -> Option<NonNull<T>> {
        unsafe {
            let start_footer = self.start_footer.as_ref();
            let chunk_ptr = start_footer.ptr.get().cast().as_ptr();

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
            let start_footer = self.start_footer.as_ref();
            self.start_footer = start_footer.next.get();

            let start_footer = self.start_footer.as_ref();
            self.ptr_or_idx = start_footer.data.cast().as_ptr();

            self.next_element_fast()
        }
    }

    #[inline(always)]
    unsafe fn prev_element_fast(&mut self) -> Option<NonNull<T>> {
        unsafe {
            let end_footer = self.end_footer.as_ref();
            let chunk_start = end_footer.data.cast().as_ptr();

            if self.end_or_len != chunk_start {
                self.end_or_len = self.end_or_len.byte_sub(Stack::<T>::ELEMENT_SIZE);
                Some(NonNull::new_unchecked(self.end_or_len as *mut T))
            } else {
                None
            }
        }
    }

    unsafe fn prev_element_slow(&mut self) -> Option<NonNull<T>> {
        unsafe {
            let end_footer = self.end_footer.as_ref();
            self.end_footer = end_footer.prev.get();

            let end_footer = self.end_footer.as_ref();
            self.end_or_len = end_footer.ptr.get().cast().as_ptr();

            self.prev_element_fast()
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
                    Some(self.start_footer.cast().as_ref())
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
                    Some(self.start_footer.cast().as_ref())
                }
            } else {
                self.ptr_or_idx = self.end_or_len;
                None
            }
        } else {
            loop {
                let start_footer = unsafe { self.start_footer.as_ref() };
                let chunk_start = start_footer.data.as_ptr() as *const T;
                let chunk_end = start_footer.ptr.get().as_ptr() as *const T;
                let ptr = self.ptr_or_idx;
                let end = self.end_or_len;

                if chunk_start <= end && end <= chunk_end {
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
                    debug_assert!(chunk_start <= ptr && ptr <= chunk_end);
                    let size = chunk_end as usize - ptr as usize;
                    if need <= size {
                        let new_ptr = ptr.wrapping_byte_add(need);
                        let ptr = ptr.wrapping_byte_add(need - Stack::<T>::ELEMENT_SIZE);
                        self.ptr_or_idx = new_ptr;
                        break Some(unsafe { &*ptr });
                    } else {
                        need -= size;
                        self.start_footer = start_footer.next.get();
                        self.ptr_or_idx =
                            unsafe { self.start_footer.as_ref().data.cast().as_ptr() };
                    }
                }
            }
        }
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if const { Stack::<T>::ELEMENT_IS_ZST } {
            // it just increments `ptr_or_idx`
            self.next()
        } else {
            if self.ptr_or_idx == self.end_or_len {
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
}
