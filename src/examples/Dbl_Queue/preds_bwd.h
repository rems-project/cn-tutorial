/*@

predicate (datatype seq) Dbl_Queue_Bwd_At (pointer l) {
    if (is_null(l)) {
        return Seq_Nil{};
    }
    else {
        take L = Owned<struct dbl_queue>(l);
        assert (   (is_null(L.front)  && is_null(L.back)) 
                || (!is_null(L.front) && !is_null(L.back)));
        take inner = Own_Front_Back_Bwds(L.front, L.back);
        return inner;
    }
}

predicate (datatype seq) Own_Front_Back_Bwds (pointer front, pointer back) {
    if (is_null(front)) {
        return Seq_Nil{};
    } else {
        if (ptr_eq(front, back)) {
            take B = Owned<struct node>(back);
            assert (is_null(B.next));
            assert (is_null(B.prev));
            return Seq_Cons {head: B.data, tail: Seq_Nil{}};
        } else {
            take B = Owned<struct node>(back);
            assert (is_null(B.next));
            take F = Owned<struct node>(front);
            assert(is_null(F.prev));
            assert(!is_null(F.next));
            assert(!is_null(B.prev));
            take Rest = Own_Inner_Bwds(B.prev, back, B, front, F);
            return Seq_Cons{ head: B.data, tail: Rest};
        }
    }
}

predicate (datatype seq) Own_Inner_Bwds(pointer p, pointer next_pointer, struct node next_node, pointer f, struct node Front) {
    if (ptr_eq(p,f)) {
        assert(ptr_eq(Front.next, next_pointer));
        assert(ptr_eq(next_node.prev, p));
        return Seq_Cons{head: Front.data, tail: Seq_Nil{}};
    } else {
        take n = Owned<struct node>(p);
        assert (ptr_eq(n.next, next_pointer));
        assert(ptr_eq(next_node.prev, p));
        assert(!is_null(n.next));
        assert(!is_null(n.prev));
        take Rest = Own_Inner_Bwds(n.prev, p, n, f, Front);
        return Seq_Cons{head: n.data, tail: Rest};
    }
}
@*/