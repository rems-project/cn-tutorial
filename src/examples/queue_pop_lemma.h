/*@
lemma snoc_facts (pointer front, pointer back, i32 x)
  requires
      take Q = QueueAux(front, back);
      take B = Owned<struct queue_cell>(back);
  ensures
      take NewQ = QueueAux(front, back);
      take NewB = Owned<struct queue_cell>(back);
      Q == NewQ; B == NewB;
      let L = Snoc (Cons{Head: x, Tail: Q}, B.first);
      Hd(L) == x;
      Tl(L) == Snoc (Q, B.first);
@*/
