/*@
lemma push_lemma (pointer front, pointer p)
  requires
      take Q = IntQueueAux(front, p);
      take P = Owned<struct queue_cell>(p);
  ensures
      take Q_post = IntQueueAux(front, P.next);
      Q_post == Snoc(Q, P.first);
@*/
