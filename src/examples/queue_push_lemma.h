/*@
lemma aux_induction(pointer front, pointer prev, pointer back, 
                    datatype seq before, i32 prev_pushed)
requires
    take Prev = Owned<struct int_queueCell>(prev);
    take Q = IntQueueAux(front, prev);
    ptr_eq(Prev.next, back);                  // sanity check
    Prev.first == prev_pushed;                // sanity check
    snoc(Q, prev_pushed) == before;           // sanity check
ensures
    take Q2 = IntQueueAux(front, back);
    before == Q2;
@*/
