/*@
lemma tl_snoc (pointer front, pointer back, datatype seq before, i32 popped)
requires
    take T = Owned<struct int_queueCell>(back);
    is_null(T.next);
    take Q = IntQueueAux(front, back);
    let after = snoc(Q, T.first);
    before == snoc (Seq_Cons{head: popped, tail: Q}, T.first);
ensures
    take T2 = Owned<struct int_queueCell>(back);
    T == T2;
    is_null(T.next);
    take Q2 = IntQueueAux(front, back);
    Q == Q2;
    after == tl(before);
    popped == hd(before);
@*/
