// TODO i32 to I32
// TODO is_null Is_Null() or Is_null()
// TODO: show people List_Int and List_Int_At and ask
// what people like better for predicate name.
// or Linked_List_Int?

// maybe keep seq? Since it goes with many different data structures. 
/*@
datatype Seq_Int {
  Nil__Seq_Int {},
  Cons__Seq_Int {i32 Head, datatype Seq_Int Tail}
}

predicate (datatype Seq_Int) Linked_List_Int(pointer p) {
  if (is_null(p)) {
    return Nil__Seq_Int{};
  } else {
    take h = Owned<struct list_int>(p);
    take Tl = Linked_List_Int(h.tail);
    return (Cons__Seq_Int { Head: h.head, Tail: Tl });
  }
}
@*/
