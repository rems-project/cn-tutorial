/* liast_rev_lemmas.h */

/*@
lemma append_nil_r (datatype seq l1)
  requires true;
  ensures append(l1, Seq_Nil {}) == l1;

lemma append_cons_r (datatype seq l1, i32 x, datatype seq l2)
  requires true;
  ensures append(l1, Seq_Cons {head: x, tail: l2})
          == append(snoc(l1, x), l2);
@*/
