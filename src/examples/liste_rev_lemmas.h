/*@
lemma append_nil_r (datatype List l1)
  requires true
  ensures append(l1, Nil {}) == l1

lemma append_cons_r (datatype List l1, i32 x, datatype List l2)
  requires true
  ensures append(l1, Cons {Head: x, Tail: l2})
          == append(snoc(l1, x), l2)
@*/
