/*@
predicate (datatype List) QueueAux (pointer f, pointer b) {
  if (ptr_eq(f,b)) {
    return Nil{};
  } else {
    take F = Owned<struct queue_cell>(f);
    assert (!is_null(F.next));  
    take B = QueueAux(F.next, b);
    return Cons{Head: F.first, Tail: B};
  }
}
@*/
