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

    let s = Stack::from(&[1, 2, 4]);
    assert!(s.capacity() >= 3);
    assert_eq!(s.len(), 3);

    let s = Stack::from([1, 2, 4].as_slice());
    assert!(s.capacity() >= 3);
    assert_eq!(s.len(), 3);
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

#[test]
fn stack_iter() {
    let stk = Stack::new();
    stk.push(0);
    let capacity_1 = stk.capacity();
    for i in 1..capacity_1 {
        stk.push(i);
    }
    assert_eq!(stk.len(), capacity_1);

    for (i, elem) in stk.iter().enumerate() {
        assert_eq!(*elem, i);
    }

    stk.push(capacity_1);
    let capacity_12 = stk.capacity();
    for i in capacity_1 + 1..capacity_12 {
        stk.push(i);
    }
    assert_eq!(stk.len(), capacity_12);

    for (i, elem) in stk.iter().enumerate() {
        assert_eq!(*elem, i);
    }

    // double the stack
    let len_before = stk.len();
    for elem in &stk {
        stk.push(*elem);
    }
    let len_after = stk.len();
    assert_eq!(2 * len_before, len_after);
}

#[test]
fn stack_iter_zst() {
    let stk = Stack::new();
    stk.push(());
    stk.push(());
    stk.push(());
    stk.push(());

    let count = stk.iter().fold(0, |count, _| count + 1);
    assert_eq!(stk.len(), count);

    let stk = Stack::new();
    stk.push(());
    stk.push(());
    stk.push(());
    stk.push(());

    let mut iter = stk.iter();
    assert_eq!((4, Some(4)), iter.size_hint());
    iter.next();
    assert_eq!((3, Some(3)), iter.size_hint());
    iter.next();
    assert_eq!((2, Some(2)), iter.size_hint());
    iter.next();
    assert_eq!((1, Some(1)), iter.size_hint());
    iter.next();
    assert_eq!((0, Some(0)), iter.size_hint());
    iter.next();
    assert_eq!((0, Some(0)), iter.size_hint());
}

#[test]
fn stack_iter_count() {
    let stk = Stack::new();
    stk.push(1);
    stk.push(2);
    stk.push(4);
    stk.push(7);
    assert_eq!(4, stk.iter().count());

    let stk = Stack::new();
    stk.push(());
    stk.push(());
    stk.push(());
    stk.push(());
    assert_eq!(4, stk.iter().count());
}

#[test]
#[allow(clippy::iter_nth_zero)]
fn stack_iter_nth() {
    // ZST
    let stk = Stack::new();
    stk.push(());
    stk.push(());
    stk.push(());
    stk.push(());
    let mut iter = stk.iter();
    assert_eq!(iter.nth(1), Some(&()));
    assert_eq!(iter.nth(1), Some(&()));
    assert_eq!(iter.nth(0), None);

    // non-ZST
    let mut stk = Stack::new();
    stk.push(0);
    let capacity = stk.capacity();
    for i in 1..capacity {
        stk.push(i);
    }

    {
        let mut iter = stk.iter();
        assert_eq!(iter.nth(1), Some(&1));
        assert_eq!(iter.nth(1), Some(&3));
        assert_eq!(iter.nth(capacity), None);

        let mut iter = stk.iter();
        assert_eq!(iter.nth(capacity - 1), Some(&(capacity - 1)));

        let mut iter = stk.iter();
        assert_eq!(iter.nth(capacity), None);

        stk.push(capacity);
        assert_ne!(stk.capacity(), capacity);

        let mut iter = stk.iter();
        assert_eq!(iter.nth(1), Some(&1));
        assert_eq!(iter.nth(1), Some(&3));
        assert_eq!(iter.nth(capacity), None);

        let mut iter = stk.iter();
        assert_eq!(iter.nth(capacity), Some(&capacity));
        assert_eq!(iter.nth(0), None);
    }

    stk.pop();
    assert_eq!(stk.len(), capacity);
    assert_ne!(stk.capacity(), capacity);

    let mut iter = stk.iter();
    assert_eq!(iter.nth(1), Some(&1));
    assert_eq!(iter.nth(1), Some(&3));
    assert_eq!(iter.nth(capacity - 4), None);
}
