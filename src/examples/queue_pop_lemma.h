/*@
lemma tl_snoc (pointer front, pointer back, i32 x)
  requires
      take Q = IntQueueAux(front, back);
      take B = Owned<struct int_queueCell>(back);
      is_null(B.next);
      let after = snoc (Q, B.first);
      let before = snoc (Seq_Cons{head: x, tail: Q}, B.first);
  ensures
      take NewQ = IntQueueAux(front, back);
      Q == NewQ;
      take NewB = Owned<struct int_queueCell>(back);
      B == NewB;
      after == tl(before);
      x == hd(before);
@*/
