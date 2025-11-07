use crate::{ChunkFooter, Stack};
use core::iter::Iterator;
use core::ptr::NonNull;

pub struct Iter<'a, T> {
    _stack: &'a Stack<T>,
    current_footer: NonNull<ChunkFooter>,
    ptr_or_cnt: *const T,
    end_or_len: *const T,
}

impl<'a, T> Iter<'a, T> {
    pub(crate) fn new(stack: &'a Stack<T>) -> Self {
        let current_footer = unsafe { stack.current_footer.get().as_ref() };
        if const { Stack::<T>::ELEMENT_IS_ZST } {
            Self {
                _stack: stack,
                current_footer: current_footer.get(),
                ptr_or_cnt: core::ptr::null(),
                end_or_len: core::ptr::without_provenance(stack.len()),
            }
        } else {
            let ptr = unsafe { stack.first_footer.get().as_ref().data.cast().as_ptr() };
            let end = current_footer.ptr.get().cast().as_ptr();
            Self {
                _stack: stack,
                current_footer: stack.first_footer.get(),
                ptr_or_cnt: ptr,
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

            if self.ptr_or_cnt != chunk_ptr {
                let ptr = self.ptr_or_cnt;
                self.ptr_or_cnt = ptr.byte_add(Stack::<T>::ELEMENT_SIZE);
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
            self.ptr_or_cnt = current_footer.data.cast().as_ptr();

            self.next_element_fast()
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if const { Stack::<T>::ELEMENT_IS_ZST } {
            if self.ptr_or_cnt < self.end_or_len {
                unsafe {
                    self.ptr_or_cnt = self.ptr_or_cnt.byte_add(1);
                    Some(self.current_footer.cast().as_ref())
                }
            } else {
                None
            }
        } else {
            if self.ptr_or_cnt == self.end_or_len {
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
}
