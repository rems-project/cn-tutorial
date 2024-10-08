/*@

predicate (datatype seq) Dbl_Queue_Fwd_At (pointer l) {
    if (is_null(l)) {
        return Seq_Nil{};
    }
    else {
        take L = Owned<struct dbl_queue>(l);
        assert (   (is_null(L.front)  && is_null(L.back)) 
                || (!is_null(L.front) && !is_null(L.back)));
        take inner = Own_Front_Back_Fwds(L.front, L.back);
        return inner;
    }
}

predicate (datatype seq) Own_Front_Back_Fwds (pointer front, pointer back) {
    if (is_null(front)) {
        return Seq_Nil{};
    } else {
        if (ptr_eq(front, back)) {
            // Only one node in the list, so only one node to own
            take F = Owned<struct node>(front);
            assert (is_null(F.next));
            assert (is_null(F.prev));
            return Seq_Cons {head: F.data, tail: Seq_Nil{}};
        } else {
            take B = Owned<struct node>(back);
            assert (is_null(B.next));
            take F = Owned<struct node>(front);
            assert(is_null(F.prev));
            assert(!is_null(F.next));
            assert(!is_null(B.prev));
            take Rest = Own_Inner_Fwds(F.next, front, F, back, B);
            return Seq_Cons{ head: F.data, tail: Rest};
        }
    }
}

predicate (datatype seq) Own_Inner_Fwds(pointer p, pointer prev_pointer, struct node prev_node, pointer b, struct node Back) {
    if (ptr_eq(p,b)) {
        assert(ptr_eq(Back.prev, prev_pointer));
         assert(ptr_eq(prev_node.next, p));
        return Seq_Cons{head: Back.data, tail: Seq_Nil{}};
    } else {
        take n = Owned<struct node>(p);
        assert (ptr_eq(n.prev, prev_pointer));
        assert(ptr_eq(prev_node.next, p));
        assert(!is_null(n.next));
        assert(!is_null(n.prev));
        take Rest = Own_Inner_Fwds(n.next, p, n, b, Back);
        return Seq_Cons{head: n.data, tail: Rest};
    }
}
@*/