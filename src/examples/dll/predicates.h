/*@
predicate (datatype Nonempty_Dll) Dll_at (pointer p) {
    if (is_null(p)) {
        return Empty_Dll{};
    } else {
        take n = Owned<struct dllist>(p);
        take Left = Own_Backwards(n.prev, p, n);
        take Right = Own_Forwards(n.next, p, n);
        return Nonempty_Dll{left: Left, curr: n, right: Right};
    }
}

predicate (datatype List) Own_Forwards (pointer p, 
                                        pointer prev_pointer, 
                                        struct dllist prev_dllist) {
    if (is_null(p)) {
        return Nil{};
    } else {
        take n = Owned<struct dllist>(p);
        assert (ptr_eq(n.prev, prev_pointer));
        assert(ptr_eq(prev_dllist.next, p));
        take Right = Own_Forwards(n.next, p, n);
        return Cons{Head: n.data, Tail: Right};
    }
}

predicate (datatype List) Own_Backwards (pointer p, 
                                         pointer next_pointer, 
                                         struct dllist next_dllist) {
    if (is_null(p)) {
        return Nil{};
    } else {
        take n = Owned<struct dllist>(p);
        assert (ptr_eq(n.next, next_pointer));
        assert(ptr_eq(next_dllist.prev, p));
        take Left = Own_Backwards(n.prev, p, n);
        return Cons{Head: n.data, Tail: Left};
    }
}
@*/
