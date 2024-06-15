/*@
predicate (datatype seq) IntQueueAux (pointer h, pointer t) {
  if (ptr_eq(h,t)) {
    return Seq_Nil{};
  } else {
    take C = Owned<struct int_queueCell>(h);
    assert (!is_null(C.next));  
    take TL = IntQueueAux(C.next, t);
    return Seq_Cons { head: C.first, tail: TL };
  }
}
@*/
