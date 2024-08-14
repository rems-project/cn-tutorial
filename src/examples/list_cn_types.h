/*@
datatype List {
  Nil {},
  Cons {i32 Head, datatype List Tail}
}

predicate (datatype List) SLList(pointer p) {
  if (is_null(p)) {
    return Nil{};
  } else {
    take H = Owned<struct sllist>(p);
    take Tl = SLList(H.tail);
    return (Cons { Head: H.head, Tail: Tl });
  }
}
@*/
