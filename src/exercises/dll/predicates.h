/*@
predicate (datatype Dll) Dll_at (pointer p) {
    if (is_null(p)) {
        return Empty_Dll{};
    } else {
        take n = RW<struct dllist>(p);
        take L = Take_Left(n.prev, p, n);
        take R = Take_Right(n.next, p, n);
        return Nonempty_Dll{left: L, curr: n, right: R};
    }
}

predicate (datatype List) Take_Right (pointer p, 
                                        pointer prev_pointer, 
                                        struct dllist prev_dllist) {
    if (is_null(p)) {
        return Nil{};
    } else {
        take P = RW<struct dllist>(p);
        assert (ptr_eq(P.prev, prev_pointer));
        assert (ptr_eq(prev_dllist.next, p));
        take T = Take_Right(P.next, p, P);
        return Cons{Head: P.data, Tail: T};
    }
}

predicate (datatype List) Take_Left (pointer p, 
                                         pointer next_pointer, 
                                         struct dllist next_dllist) {
    if (is_null(p)) {
        return Nil{};
    } else {
        take P = RW<struct dllist>(p);
        assert (ptr_eq(P.next, next_pointer));
        assert (ptr_eq(next_dllist.prev, p));
        take T = Take_Left(P.prev, p, P);
        return Cons{Head: P.data, Tail: T};
    }
}
@*/
