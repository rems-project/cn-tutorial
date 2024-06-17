/*@
lemma snoc_facts (pointer front, pointer back, i32 x)
  requires
      take Q = IntQueueAux(front, back);
      take B = Owned<struct int_queueCell>(back);
  ensures
      take NewQ = IntQueueAux(front, back);
      take NewB = Owned<struct int_queueCell>(back);
      Q == NewQ; B == NewB;
      let L = snoc (Seq_Cons{head: x, tail: Q}, B.first);
      hd(L) == x;
      tl(L) == snoc (Q, B.first);
@*/
