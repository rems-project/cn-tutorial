/*@
predicate (datatype seq) IntQueueAux (pointer f, pointer b) {
  if (ptr_eq(f,b)) {
    return Seq_Nil{};
  } else {
    take F = Owned<struct int_queueCell>(f);
    assert (!is_null(F.next));  
    take B = IntQueueAux(F.next, b);
    return Seq_Cons{head: F.first, tail: B};
  }
}
@*/
