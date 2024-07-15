/*@
predicate (datatype Dll) LinkedList (pointer p) {
    if (is_null(p)) {
        return Empty_Dll{};
    } else {
        take n = Owned<struct node>(p);
        take First = Own_Backwards(n.prev, p, n);
        take Rest = Own_Forwards(n.next, p, n);
        return Dll{first: First, n: n, rest: Rest};
    }
}

predicate (datatype Seq_Node) Own_Forwards(pointer p, pointer prev_pointer, struct node prev_node) {
    if (is_null(p)) {
        return Seq_Node_Nil{};
    } else {
        take n = Owned<struct node>(p);
        assert (ptr_eq(n.prev, prev_pointer));
        assert(ptr_eq(prev_node.next,p));
        take Rest = Own_Forwards_Aux(n.next, p, n);
        return Seq_Node_Cons{n: n, tail: Rest};
    }
}

predicate (datatype seq) Own_Forwards_Aux(pointer p, pointer prev_pointer, struct node prev_node) {
    if (is_null(p)) {
        return Seq_Nil{};
    } else {
        take n = Owned<struct node>(p);
        assert (ptr_eq(n.prev, prev_pointer));
        assert(ptr_eq(prev_node.next, p));
        take Rest = Own_Forwards_Aux(n.next, p, n);
        return Seq_Cons{head: n.data, tail: Rest};
    }
}



predicate (datatype Seq_Node) Own_Backwards(pointer p, pointer next_pointer, struct node next_node) {
    if (is_null(p)) {
        return Seq_Node_Nil{};
    } else {
        take n = Owned<struct node>(p);
        assert (ptr_eq(n.next, next_pointer));
        assert(ptr_eq(next_node.prev, p));
        take First = Own_Backwards_Aux(n.prev, p, n);
        return Seq_Node_Cons{n: n, tail: First};
    }
}

predicate (datatype seq) Own_Backwards_Aux(pointer p, pointer next_pointer, struct node next_node) {
    if (is_null(p)) {
        return Seq_Nil{};
    } else {
        take n = Owned<struct node>(p);
        assert (ptr_eq(n.next, next_pointer));
        assert(ptr_eq(next_node.prev, p));
        take First = Own_Backwards_Aux(n.prev, p, n);
        return Seq_Cons{head: n.data, tail: First};
    }
}
@*/