/*@
predicate (datatype Dll) Dll_at (pointer p) {
    if (is_null(p)) {
        return Empty_Dll{};
    } else {
        take n = Owned<struct dllist>(p);
        take L = Own_Backwards(n.prev, p, n);
        take R = Own_Forwards(n.next, p, n);
        return Nonempty_Dll{left: L, curr: n, right: R};
    }
}

predicate (datatype List) Own_Forwards (pointer p, 
                                        pointer prev_pointer, 
                                        struct dllist prev_dllist) {
    if (is_null(p)) {
        return Nil{};
    } else {
        take P = Owned<struct dllist>(p);
        assert (ptr_eq(P.prev, prev_pointer));
        assert(ptr_eq(prev_dllist.next, p));
        take T = Own_Forwards(P.next, p, P);
        return Cons{Head: P.data, Tail: T};
    }
}

predicate (datatype List) Own_Backwards (pointer p, 
                                         pointer next_pointer, 
                                         struct dllist next_dllist) {
    if (is_null(p)) {
        return Nil{};
    } else {
        take P = Owned<struct dllist>(p);
        assert (ptr_eq(P.next, next_pointer));
        assert(ptr_eq(next_dllist.prev, p));
        take T = Own_Backwards(P.prev, p, P);
        return Cons{Head: P.data, Tail: T};
    }
}
@*/
