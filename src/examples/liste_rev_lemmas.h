/*@
lemma Append_nil_r (datatype List l1)
  requires true
  ensures Append(l1, Nil {}) == l1

lemma Append_cons_r (datatype List l1, i32 x, datatype List l2)
  requires true
  ensures Append(l1, Cons {Head: x, Tail: l2})
          == Append(snoc(l1, x), l2)
@*/
