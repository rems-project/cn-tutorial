/*@
datatype List {
  Nil {},
  Cons {i32 Head, datatype List Tail}
}

predicate (datatype List) SLList_At(pointer p) {
  if (is_null(p)) {
    return Nil{};
  } else {
    take H = RW<struct sllist>(p);
    take T = SLList_At(H.tail);
    return (Cons { Head: H.head, Tail: T });
  }
}
@*/
