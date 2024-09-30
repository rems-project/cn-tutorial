/*@
lemma push_lemma (pointer front, pointer p)
  requires
      ptr_eq(front, p) || !addr_eq(front, p);
      take Q = IntQueueAux(front, p);
      take P = Owned<struct int_queueCell>(p);
  ensures
      ptr_eq(front, P.next) || !addr_eq(front, P.next);
      take NewQ = IntQueueAux(front, P.next);
      NewQ == snoc(Q, P.first);
@*/
