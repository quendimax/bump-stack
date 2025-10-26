#![cfg(test)]

use super::*;
use pretty_assertions::assert_eq;

#[test]
fn stack_new() {
    let stack = Stack::<u8>::new();
    unsafe {
        assert!(stack.current_footer.as_ref().is_empty());
        assert!(core::ptr::eq(stack.current_footer.as_ptr(), &EMPTY_CHUNK.0));
    }
    assert!(stack.is_empty());
}

#[test]
fn stack_push() {
    let mut stack = Stack::<u32>::new();
    assert_eq!(stack.capacity(), 0);
    assert_eq!(stack.len(), 0);

    stack.push(1);
    let capacity = stack.capacity();
    assert!(capacity >= 8);
    assert_eq!(stack.len(), 1);

    stack.push(2);
    assert_eq!(stack.capacity(), capacity);
    assert_eq!(stack.len(), 2);

    stack.push_with(|| 2);
    assert_eq!(stack.capacity(), capacity);
    assert_eq!(stack.len(), 3);
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
