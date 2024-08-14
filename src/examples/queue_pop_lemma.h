/*@
lemma snoc_facts (pointer front, pointer back, i32 x)
  requires
      take Q = IntQueueAux(front, back);
      take B = Owned<struct int_queueCell>(back);
  ensures
      take NewQ = IntQueueAux(front, back);
      take NewB = Owned<struct int_queueCell>(back);
      Q == NewQ; B == NewB;
      let L = Snoc (Cons{Head: x, Tail: Q}, B.first);
      Hd(L) == x;
      Tl(L) == Snoc (Q, B.first);
@*/
