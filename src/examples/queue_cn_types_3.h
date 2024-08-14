/*@
predicate (datatype List) IntQueueAux (pointer f, pointer b) {
  if (ptr_eq(f,b)) {
    return Nil{};
  } else {
    take F = Owned<struct int_queueCell>(f);
    assert (!is_null(F.next));  
    take B = IntQueueAux(F.next, b);
    return Cons{Head: F.first, Tail: B};
  }
}
@*/
