/*@
lemma push_lemma (pointer front, pointer p)
  requires
      take Q = IntQueueAux(front, p);
      take P = Owned<struct int_queueCell>(p);
  ensures
      take Q_post = IntQueueAux(front, P.next);
      NewQ == Snoc(Q, P.first);
@*/
