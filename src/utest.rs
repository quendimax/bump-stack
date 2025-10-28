#![cfg(test)]

use super::*;
use pretty_assertions::assert_eq;

#[test]
fn stack_without_chunks() {
    let stack = Stack::<u8>::new();
    unsafe {
        assert!(stack.current_footer.get().as_ref().is_none());
        assert!(core::ptr::eq(
            stack.current_footer.get().as_ptr(),
            &NONE_CHUNK.0
        ),);
    }
    assert!(stack.is_empty());
}

#[test]
fn stack_one_chunk() {
    type Stack = super::Stack<usize>;
    let mut stack = Stack::new();
    assert_eq!(stack.capacity(), 0);
    assert_eq!(stack.len(), 0);

    unsafe {
        assert!(stack.current_footer.get().as_ref().is_none());
        assert!(stack.current_footer.get().as_ref().is_empty());
    }

    stack.push(0);
    let capacity = stack.capacity();

    debug_assert!(capacity > 1);

    for i in 1..capacity {
        unsafe {
            assert!(!stack.current_footer.get().as_ref().is_none());
            assert!(stack.current_footer.get().as_ref().remains() >= Stack::ELEMENT_SIZE);
        }
        stack.push(i);

        assert_eq!(stack.capacity(), capacity);
        assert_eq!(stack.len(), i + 1);
    }

    unsafe {
        let current_footer = stack.current_footer.get().as_ref();
        assert!(!current_footer.is_none());
        assert!(current_footer.remains() < Stack::ELEMENT_SIZE);
        assert!(current_footer.prev.get().as_ref().is_none());
        assert!(current_footer.next.get().as_ref().is_none());
    }

    for i in (0..capacity).rev() {
        unsafe {
            assert!(!stack.current_footer.get().as_ref().is_none());
        }
        assert_eq!(stack.pop(), Some(i));
        assert_eq!(stack.len(), i);
    }
    assert!(stack.is_empty());
    unsafe {
        let current_footer = stack.current_footer.get().as_ref();
        assert!(!current_footer.is_none());
        assert!(current_footer.prev.get().as_ref().is_none());
        assert!(current_footer.next.get().as_ref().is_none());
    }
}

#[test]
fn stack_two_chunk() {
    #[derive(Debug, PartialEq, Eq)]
    struct Element {
        _value: [usize; 6],
    }

    fn elem(i: usize) -> Element {
        Element { _value: [i; 6] }
    }

    type Stack = super::Stack<Element>;
    let mut stack = Stack::new();

    stack.push(elem(0));
    let capacity = stack.capacity();

    for i in 1..capacity + 1 {
        stack.push(elem(i));
    }

    let capacity_2 = stack.capacity();
    assert!(capacity < capacity_2);

    unsafe {
        let current_footer = stack.current_footer.get().as_ref();
        assert!(!current_footer.is_none());
        assert!(!current_footer.prev.get().as_ref().is_none());
        assert!(current_footer.next.get().as_ref().is_none());
    }

    for i in capacity + 1..capacity_2 {
        stack.push(elem(i));
    }

    assert_eq!(stack.capacity(), capacity_2);
    assert_eq!(stack.len(), capacity_2);

    for i in (capacity..capacity_2).rev() {
        assert_eq!(stack.pop(), Some(elem(i)));
    }

    assert_eq!(stack.capacity(), capacity_2);
    assert_eq!(stack.len(), capacity);

    unsafe {
        let current_footer = stack.current_footer.get().as_ref();
        assert!(!current_footer.is_none());
        assert!(!current_footer.prev.get().as_ref().is_none());
        assert!(current_footer.next.get().as_ref().is_none());
    }

    for i in (0..capacity).rev() {
        assert_eq!(stack.pop(), Some(elem(i)));
    }

    assert_eq!(stack.capacity(), capacity_2);
    assert_eq!(stack.len(), 0);

    stack.pop();

    // should stay the biggest chunk
    assert_eq!(stack.capacity(), capacity_2 - capacity);
    assert_eq!(stack.len(), 0);

    unsafe {
        let current_footer = stack.current_footer.get().as_ref();
        assert!(!current_footer.is_none());
        assert!(current_footer.prev.get().as_ref().is_none());
        assert!(current_footer.next.get().as_ref().is_none());
    }
}
