// TODO i32 to I32
// TODO is_null to Is_Null() or Is_null()
// TODO: show people List_Int and List_Int_At and ask
//       which is better for predicate name.
//       (But perhaps Linked_List_Int is clearest?)

// We've kept Seq for the type of abstract sequences, since many
// different concrete data structures are representations of abstract
// lists.

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
