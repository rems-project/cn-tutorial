// We've kept Seq for the type of abstract sequences, since many
// different concrete data structures are representations of abstract
// lists.

/*@
datatype List {
  Nil {},
  Cons {i32 Head, datatype List Tail}
}

predicate (datatype List) SLList(pointer p) {
  if (is_null(p)) {
    return Nil{};
  } else {
    take h = Owned<struct sllist>(p);
    take Tl = SLList(h.tail);
    return (Cons { Head: h.head, Tail: Tl });
  }
}
@*/
