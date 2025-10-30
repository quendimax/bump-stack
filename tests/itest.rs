use bump_stack::Stack;

#[test]
fn stack_ctor() {
    let s = Stack::<i32>::new();
    assert_eq!(s.capacity(), 0);
    assert_eq!(s.len(), 0);

    let s = Stack::<i32>::default();
    assert_eq!(s.capacity(), 0);
    assert_eq!(s.len(), 0);

    let s = Stack::<()>::default();
    assert_eq!(s.capacity(), usize::MAX);
    assert_eq!(s.len(), 0);

    let s = Stack::<i32>::with_capacity(10);
    assert!(s.capacity() >= 10);
    assert_eq!(s.len(), 0);

    let s = Stack::<()>::with_capacity(10);
    assert_eq!(s.capacity(), usize::MAX);
    assert_eq!(s.len(), 0);
}

#[test]
fn stack_push_pop() {
    let mut stack = Stack::default();
    const MAX: usize = 1 << 10;
    for i in 0..MAX {
        assert_eq!(stack.len(), i);
        stack.push(i);
    }
    for i in (0..MAX).rev() {
        assert_eq!(stack.pop(), Some(i));
    }
    assert_eq!(stack.len(), 0);
    assert!(stack.len() < stack.capacity());
}
