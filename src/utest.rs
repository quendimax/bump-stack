use super::*;
use pretty_assertions::assert_eq;

#[test]
fn stack_without_chunks() {
    let stack = Stack::<u8>::new();
    unsafe {
        assert!(stack.current_footer.as_ref().is_dead());
        assert!(core::ptr::eq(stack.current_footer.as_ptr(), &DEAD_CHUNK.0),);
    }
    assert!(stack.is_empty());
}

#[test]
fn stack_one_chunk() {
    type Stack = super::Stack<usize>;
    const ELEMENT_SIZE: usize = super::Stack::<usize>::ELEMENT_SIZE;
    let mut stack = Stack::new();
    assert_eq!(stack.capacity(), 0);
    assert_eq!(stack.len(), 0);

    unsafe {
        assert!(stack.current_footer.as_ref().is_dead());
        assert!(stack.current_footer.as_ref().occupied() < ELEMENT_SIZE);
    }

    stack.push(0);
    let capacity = stack.capacity();

    debug_assert!(capacity > 1);

    for i in 1..capacity {
        unsafe {
            assert!(!stack.current_footer.as_ref().is_dead());
            assert!(stack.current_footer.as_ref().remains() >= Stack::ELEMENT_SIZE);
        }
        stack.push(i);

        assert_eq!(stack.capacity(), capacity);
        assert_eq!(stack.len(), i + 1);
    }

    unsafe {
        let current_footer = stack.current_footer.as_ref();
        assert!(!current_footer.is_dead());
        assert!(current_footer.remains() < Stack::ELEMENT_SIZE);
        assert!(current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
    }

    for i in (0..capacity).rev() {
        unsafe {
            assert!(!stack.current_footer.as_ref().is_dead());
        }
        assert_eq!(stack.pop(), Some(i));
        assert_eq!(stack.len(), i);
    }
    assert!(stack.is_empty());
    unsafe {
        let current_footer = stack.current_footer.as_ref();
        assert!(!current_footer.is_dead());
        assert!(current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
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
    let capacity = stack.capacity();

    for i in 1..capacity + 1 {
        stack.push(elem(i));
    }

    let capacity_2 = stack.capacity();
    assert!(capacity < capacity_2);

    unsafe {
        let current_footer = stack.current_footer.as_ref();
        assert!(!current_footer.is_dead());
        assert!(!current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
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
        let current_footer = stack.current_footer.as_ref();
        assert!(!current_footer.is_dead());
        assert!(!current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
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
        let current_footer = stack.current_footer.as_ref();
        assert!(!current_footer.is_dead());
        assert!(current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
    }
}

#[test]
fn stack_three_chunks() {
    let mut stack = Stack::<Element>::new();
    const ELEMENT_SIZE: usize = Stack::<Element>::ELEMENT_SIZE;

    stack.push(elem(0));
    let capacity_1 = stack.capacity();

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
        let current_footer = stack.current_footer.as_ref();
        assert!(!current_footer.is_dead());
        assert!(!current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
    }

    for i in (capacity_12..capacity_123).rev() {
        assert_eq!(stack.pop(), Some(elem(i)));
    }

    assert_eq!(stack.len(), capacity_12);
    assert_eq!(stack.capacity(), capacity_123);

    unsafe {
        let current_footer = stack.current_footer.as_ref();
        assert!(!current_footer.is_dead());
        assert!(current_footer.occupied() < ELEMENT_SIZE);
        assert!(!current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
    }

    for i in (capacity_1..capacity_12).rev() {
        assert_eq!(stack.pop(), Some(elem(i)));
    }

    assert_eq!(stack.len(), capacity_1);
    assert_eq!(stack.capacity(), capacity_123);

    unsafe {
        let current_footer = stack.current_footer.as_ref();
        assert!(!current_footer.is_dead());
        assert!(current_footer.occupied() < ELEMENT_SIZE);
        assert!(!current_footer.prev.get().as_ref().is_dead());
        assert!(!current_footer.next.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().occupied() < ELEMENT_SIZE);
    }

    for i in (0..capacity_1).rev() {
        assert_eq!(stack.pop(), Some(elem(i)));
    }

    let capacity_13 = capacity_123 - capacity_12 + capacity_1;

    assert_eq!(stack.capacity(), capacity_13);
    assert_eq!(stack.len(), 0);

    unsafe {
        let current_footer = stack.current_footer.as_ref();
        assert!(!current_footer.is_dead());
        assert!(current_footer.occupied() < ELEMENT_SIZE);
        assert!(current_footer.prev.get().as_ref().is_dead());
        let next_footer = current_footer.next.get().as_ref();
        assert!(!next_footer.is_dead());
        assert!(next_footer.occupied() < ELEMENT_SIZE);
        assert_eq!(next_footer.prev.get(), stack.current_footer);
        assert!(next_footer.next.get().as_ref().is_dead());
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
        let current_footer = stack.current_footer.as_ref();
        assert!(current_footer.is_dead());
        assert!(current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
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
        let current_footer = stack.current_footer.as_ref();
        assert!(current_footer.is_dead());
        assert!(current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
    }
}

#[test]
fn stack_with_capacity() {
    let stack = Stack::<i32>::with_capacity(0);
    unsafe {
        assert!(stack.current_footer.as_ref().is_dead());
    }

    let stack = Stack::<i32>::with_capacity(1);
    unsafe {
        let current_footer = stack.current_footer.as_ref();
        assert!(!current_footer.is_dead());
        assert!(current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
    }

    let stack = Stack::<usize>::with_capacity(1 << 20);
    assert!(stack.capacity() >= 1 << 20);
    unsafe {
        let current_footer = stack.current_footer.as_ref();
        assert!(!current_footer.is_dead());
        assert!(current_footer.prev.get().as_ref().is_dead());
        assert!(current_footer.next.get().as_ref().is_dead());
    }
}
