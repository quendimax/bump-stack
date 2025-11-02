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

    let stack = Stack::default();
    stack.push(42);
}

#[test]
fn stack_first() {
    let mut stack = Stack::default();
    assert_eq!(stack.first(), None);
    stack.push(42);
    assert_eq!(stack.first(), Some(&42));
    stack.push(24);
    assert_eq!(stack.first(), Some(&42));
    stack.pop();
    assert_eq!(stack.first(), Some(&42));
    stack.pop();
    assert_eq!(stack.first(), None);
    stack.pop();
    assert_eq!(stack.first(), None);

    let mut stack = Stack::<()>::default();
    assert_eq!(stack.first(), None);
    stack.push(());
    assert_eq!(stack.first(), Some(&()));
    stack.push(());
    assert_eq!(stack.first(), Some(&()));
    stack.pop();
    assert_eq!(stack.first(), Some(&()));
    stack.pop();
    assert_eq!(stack.first(), None);
    stack.pop();
    assert_eq!(stack.first(), None);
}

#[test]
fn stack_first_mut() {
    let mut stack = Stack::default();
    assert_eq!(stack.first_mut(), None);
    stack.push(42);
    assert_eq!(stack.first_mut(), Some(&mut 42));
    if let Some(first) = stack.first_mut() {
        assert_eq!(first, &mut 42);
        *first = 24;
    }
    assert_eq!(stack.first_mut(), Some(&mut 24));
}

#[test]
fn stack_last() {
    let mut stack = Stack::default();
    assert_eq!(stack.last(), None);

    stack.push(0);
    let capacity = stack.capacity();

    for i in 1..capacity + 1 {
        stack.push(i);
        assert_eq!(stack.last(), Some(&i));
    }

    for i in (0..capacity + 1).rev() {
        assert_eq!(stack.last(), Some(&i));
        stack.pop();
    }
    assert_eq!(stack.last(), None);

    let mut stack = Stack::<()>::default();
    assert_eq!(stack.last(), None);
    stack.push(());
    assert_eq!(stack.last(), Some(&()));
    stack.pop();
    assert_eq!(stack.last(), None);
}

#[test]
fn stack_last_mut() {
    let mut stk = Stack::new();
    assert_eq!(None, stk.last_mut());

    stk.push(5);
    assert_eq!(Some(&mut 5), stk.last_mut());

    if let Some(last) = stk.last_mut() {
        *last = 10;
    }
    assert_eq!(Some(&mut 10), stk.last_mut());

    stk.pop();
    assert_eq!(None, stk.last_mut());
}
