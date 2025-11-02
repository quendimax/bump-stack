use super::*;
use core::mem::size_of;
use pretty_assertions::{assert_eq, assert_ne};
use util::const_assert;

#[test]
fn stack_without_chunks() {
    let stack = Stack::<u8>::new();
    unsafe {
        assert!(stack.current_footer.get().as_ref().is_dead());
        assert!(core::ptr::eq(
            stack.current_footer.get().as_ptr(),
            &DEAD_CHUNK.0
        ));
        assert!(core::ptr::eq(
            stack.first_footer.get().as_ptr(),
            &DEAD_CHUNK.0
        ));
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
        assert!(stack.current_footer.get().as_ref().is_dead());
        assert!(stack.current_footer.get().as_ref().is_empty());
        assert!(stack.first_footer.get().as_ref().is_dead());
    }

    stack.push(0);
    let capacity = stack.capacity();

    debug_assert!(capacity > 1);

    for i in 1..capacity {
        unsafe {
            assert!(!stack.current_footer.get().as_ref().is_dead());
            assert!(!Stack::chunk_is_full(stack.current_footer.get().as_ref()));
            assert_eq!(stack.first_footer, stack.current_footer);
        }
        stack.push(i);

        assert_eq!(stack.capacity(), capacity);
        assert_eq!(stack.len(), i + 1);
    }

    unsafe {
        let current_footer = stack.current_footer.get().as_ref();
        assert!(!current_footer.is_dead());
        assert!(Stack::chunk_is_full(current_footer));
        assert!(current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
        assert_eq!(stack.first_footer, stack.current_footer);
    }

    for i in (0..capacity).rev() {
        unsafe {
            assert!(!stack.current_footer.get().as_ref().is_dead());
        }
        assert_eq!(stack.pop(), Some(i));
        assert_eq!(stack.len(), i);
    }
    assert!(stack.is_empty());
    unsafe {
        let current_footer = stack.current_footer.get().as_ref();
        assert!(!current_footer.is_dead());
        assert!(current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
        assert_eq!(stack.first_footer, stack.current_footer);
    }
}

#[derive(Debug, PartialEq, Eq)]
struct Element {
    _value: [usize; 6],
}

fn elem(i: usize) -> Element {
    Element { _value: [i; 6] }
}

#[test]
fn stack_two_chunks() {
    let mut stack = Stack::<Element>::new();

    stack.push(elem(0));
    let capacity_1 = stack.capacity();

    assert_eq!(stack.first_footer, stack.current_footer);

    for i in 1..capacity_1 + 1 {
        stack.push(elem(i));
    }

    let capacity_12 = stack.capacity();
    assert!(capacity_1 < capacity_12);

    unsafe {
        let current_footer = stack.current_footer.get().as_ref();
        assert!(!current_footer.is_dead());
        assert!(!current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
        assert_eq!(stack.first_footer, current_footer.prev);
    }

    for i in capacity_1 + 1..capacity_12 {
        stack.push(elem(i));
    }

    assert_eq!(stack.capacity(), capacity_12);
    assert_eq!(stack.len(), capacity_12);

    for i in (capacity_1..capacity_12).rev() {
        assert_eq!(stack.pop(), Some(elem(i)));
    }

    assert_eq!(stack.capacity(), capacity_12);
    assert_eq!(stack.len(), capacity_1);

    unsafe {
        let current_footer = stack.current_footer.get().as_ref();
        assert!(!current_footer.is_dead());
        assert!(!current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
        assert_eq!(stack.first_footer, current_footer.prev);
    }

    for i in (0..capacity_1).rev() {
        assert_eq!(stack.pop(), Some(elem(i)));
    }

    assert_eq!(stack.capacity(), capacity_12);
    assert_eq!(stack.len(), 0);

    stack.pop();

    // should stay the biggest chunk
    assert_eq!(stack.capacity(), capacity_12 - capacity_1);
    assert_eq!(stack.len(), 0);

    unsafe {
        let current_footer = stack.current_footer.get().as_ref();
        assert!(!current_footer.is_dead());
        assert!(current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
        assert_eq!(stack.first_footer, stack.current_footer);
    }
}

#[test]
fn stack_three_chunks() {
    let mut stack = Stack::<Element>::new();

    stack.push(elem(0));
    let capacity_1 = stack.capacity();
    assert_eq!(stack.first_footer, stack.current_footer);

    for i in 1..capacity_1 + 1 {
        stack.push(elem(i));
    }

    let capacity_12 = stack.capacity();

    for i in capacity_1 + 1..capacity_12 + 1 {
        stack.push(elem(i));
    }

    let capacity_123 = stack.capacity();
    assert!(capacity_12 < capacity_123);

    for i in capacity_12 + 1..capacity_123 {
        assert_eq!(stack.len(), i);
        stack.push(elem(i));
        assert_eq!(stack.capacity(), capacity_123);
    }

    assert_eq!(stack.len(), stack.capacity());
    assert_eq!(stack.capacity(), capacity_123);

    unsafe {
        let current_footer = stack.current_footer.get().as_ref();
        assert!(!current_footer.is_dead());
        assert!(!current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
        assert_eq!(stack.first_footer, current_footer.prev.get().as_ref().prev);
    }

    for i in (capacity_12..capacity_123).rev() {
        assert_eq!(stack.pop(), Some(elem(i)));
    }

    assert_eq!(stack.len(), capacity_12);
    assert_eq!(stack.capacity(), capacity_123);

    unsafe {
        let current_footer = stack.current_footer.get().as_ref();
        assert!(!current_footer.is_dead());
        assert!(current_footer.is_empty());
        assert!(!current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
        assert_eq!(stack.first_footer, current_footer.prev.get().as_ref().prev);
    }

    assert_eq!(stack.pop(), Some(elem(capacity_12 - 1)));
    stack.push(elem(capacity_12 - 1));
    stack.push(elem(capacity_12));

    unsafe {
        let current_footer = stack.current_footer.get().as_ref();
        assert!(!current_footer.is_dead());
        assert!(!current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
    }

    assert_eq!(stack.pop(), Some(elem(capacity_12)));

    for i in (capacity_1..capacity_12).rev() {
        assert_eq!(stack.pop(), Some(elem(i)));
    }

    assert_eq!(stack.len(), capacity_1);
    assert_eq!(stack.capacity(), capacity_123);

    unsafe {
        let current_footer = stack.current_footer.get().as_ref();
        assert!(!current_footer.is_dead());
        assert!(current_footer.is_empty());
        assert!(!current_footer.prev.get().as_ref().is_dead());
        assert!(!current_footer.next.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_empty());
        assert_eq!(stack.first_footer, current_footer.prev);
    }

    for i in (0..capacity_1).rev() {
        assert_eq!(stack.pop(), Some(elem(i)));
    }

    let capacity_13 = capacity_123 - capacity_12 + capacity_1;

    assert_eq!(stack.capacity(), capacity_13);
    assert_eq!(stack.len(), 0);

    unsafe {
        let current_footer = stack.current_footer.get().as_ref();
        assert!(!current_footer.is_dead());
        assert!(current_footer.is_empty());
        assert!(current_footer.prev.get().as_ref().is_dead());
        let next_footer = current_footer.next.get().as_ref();
        assert!(!next_footer.is_dead());
        assert!(next_footer.is_empty());
        assert_eq!(next_footer.prev.get(), stack.current_footer.get());
        assert!(next_footer.next.get().as_ref().is_dead());
        assert_eq!(stack.first_footer, stack.current_footer);
    }
}

#[test]
fn zero_sized_element() {
    let mut stack = Stack::<()>::default();
    assert_eq!(stack.capacity(), usize::MAX);
    assert_eq!(stack.len(), 0);

    const COUNT: usize = 200;
    for i in 0..COUNT {
        assert_eq!(stack.len(), i);
        stack.push(());
        assert_eq!(stack.capacity(), usize::MAX);
    }

    unsafe {
        let current_footer = stack.current_footer.get().as_ref();
        assert!(current_footer.is_dead());
        assert!(current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
        assert_eq!(stack.first_footer, stack.current_footer);
    }

    for i in (0..COUNT).rev() {
        assert_eq!(stack.pop(), Some(()));
        assert_eq!(stack.len(), i);
        assert_eq!(stack.capacity(), usize::MAX);
    }
    assert_eq!(stack.pop(), None);
    assert_eq!(stack.len(), 0);
    assert_eq!(stack.capacity(), usize::MAX);

    unsafe {
        let current_footer = stack.current_footer.get().as_ref();
        assert!(current_footer.is_dead());
        assert!(current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
        assert_eq!(stack.first_footer, stack.current_footer);
    }
}

#[test]
fn stack_with_capacity() {
    let stack = Stack::<i32>::with_capacity(0);
    unsafe {
        assert!(stack.current_footer.get().as_ref().is_dead());
    }

    let stack = Stack::<i32>::with_capacity(1);
    unsafe {
        let current_footer = stack.current_footer.get().as_ref();
        assert!(!current_footer.is_dead());
        assert!(current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
    }

    let stack = Stack::<usize>::with_capacity(1 << 20);
    assert!(stack.capacity() >= 1 << 20);
    unsafe {
        let current_footer = stack.current_footer.get().as_ref();
        assert!(!current_footer.is_dead());
        assert!(current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
    }
}

#[test]
fn check_alignments() {
    #[repr(C)]
    #[repr(packed(1))]
    struct T5Packed {
        _m0: u32,
        _m1: u8,
    }
    assert_eq!(size_of::<T5Packed>(), 5);

    let stk = Stack::<T5Packed>::new();
    stk.push(T5Packed { _m0: 0, _m1: 0 });

    const_assert!(!Stack::<T5Packed>::FOOTER_IS_END);
    assert_eq!(stk.capacity(), 89);
    unsafe {
        let footer = stk.current_footer.get().as_ref();
        let end = footer
            .data
            .as_ptr()
            .byte_add(stk.capacity() * size_of::<T5Packed>());
        assert_ne!(end, footer.get().cast().as_ptr());
    }

    #[repr(align(16))]
    struct T5 {
        _m0: u32,
        _m1: u8,
    }
    assert_eq!(size_of::<T5>(), 16);

    let stk = Stack::<T5>::new();
    stk.push(T5 { _m0: 0, _m1: 0 });

    const_assert!(Stack::<T5>::FOOTER_IS_END);
    assert_eq!(stk.capacity(), 28);
    unsafe {
        let footer = stk.current_footer.get().as_ref();
        let end = footer
            .data
            .as_ptr()
            .byte_add(stk.capacity() * size_of::<T5>());
        assert_eq!(end, footer.get().cast().as_ptr());
    }

    let stk = Stack::<usize>::new();
    stk.push(0);

    const_assert!(Stack::<usize>::FOOTER_IS_END);
    assert_eq!(stk.capacity(), 56);
    unsafe {
        let footer = stk.current_footer.get().as_ref();
        let end = footer
            .data
            .as_ptr()
            .byte_add(stk.capacity() * size_of::<usize>());
        assert_eq!(end, footer.get().cast().as_ptr());
    }

    let stk = Stack::<u8>::new();
    stk.push(0);

    const_assert!(Stack::<u8>::FOOTER_IS_END);
    assert_eq!(stk.capacity(), 448);
    unsafe {
        let footer = stk.current_footer.get().as_ref();
        let end = footer
            .data
            .as_ptr()
            .byte_add(stk.capacity() * size_of::<u8>());
        assert_eq!(end, footer.get().cast().as_ptr());
    }
}
