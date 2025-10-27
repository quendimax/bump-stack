#![cfg(test)]

use super::*;
use pretty_assertions::assert_eq;

#[test]
fn stack_without_chunks() {
    let stack = Stack::<u8>::new();
    unsafe {
        assert!(stack.current_footer.as_ref().is_none());
        assert!(core::ptr::eq(stack.current_footer.as_ptr(), &NONE_CHUNK.0));
    }
    assert!(stack.is_empty());
}

#[test]
fn stack_with_one_chunk() {
    type Stack = super::Stack<usize>;
    let mut stack = Stack::new();
    assert_eq!(stack.capacity(), 0);
    assert_eq!(stack.len(), 0);

    unsafe {
        assert!(stack.current_footer.as_ref().is_none());
        assert!(stack.current_footer.as_ref().is_empty());
    }

    stack.push(0);
    let capacity = stack.capacity();

    for i in 1..capacity {
        unsafe {
            assert!(!stack.current_footer.as_ref().is_none());
            assert!(stack.current_footer.as_ref().remains() >= Stack::ELEMENT_SIZE);
        }
        stack.push(i);

        assert_eq!(stack.capacity(), capacity);
        assert_eq!(stack.len(), i + 1);
    }

    unsafe {
        let current_footer = stack.current_footer.as_ref();
        assert!(!current_footer.is_none());
        assert!(current_footer.remains() < Stack::ELEMENT_SIZE);
        assert!(current_footer.prev.get().as_ref().is_none());
        assert!(current_footer.next.get().as_ref().is_none());
    }
}

#[test]
fn stack_pop() {
    let mut stack = Stack::<u32>::new();
    for i in 0..8 {
        stack.push(i);
    }
    assert_eq!(stack.len(), 8);

    let mut j = 8;
    while let Some(i) = stack.pop() {
        j -= 1;
        assert_eq!(i, j);
    }
    assert_eq!(j, 0);
}
