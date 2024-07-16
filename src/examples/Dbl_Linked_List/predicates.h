/*@
predicate (datatype Dll) Dll_at (pointer p) {
    if (is_null(p)) {
        return Empty_Dll{};
    } else {
        take n = Owned<struct node>(p);
        take Left = Own_Backwards(n.prev, p, n);
        take Right = Own_Forwards(n.next, p, n);
        return Dll{left: Left, curr: n, right: Right};
    }
}

predicate (datatype seq) Own_Forwards(pointer p, pointer prev_pointer, struct node prev_node) {
    if (is_null(p)) {
        return Seq_Nil{};
    } else {
        take n = Owned<struct node>(p);
        assert (ptr_eq(n.prev, prev_pointer));
        assert(ptr_eq(prev_node.next, p));
        take Right = Own_Forwards(n.next, p, n);
        return Seq_Cons{head: n.data, tail: Right};
    }
}

predicate (datatype seq) Own_Backwards(pointer p, pointer next_pointer, struct node next_node) {
    if (is_null(p)) {
        return Seq_Nil{};
    } else {
        take n = Owned<struct node>(p);
        assert (ptr_eq(n.next, next_pointer));
        assert(ptr_eq(next_node.prev, p));
        take Left = Own_Backwards(n.prev, p, n);
        return Seq_Cons{head: n.data, tail: Left};
    }
}
@*/