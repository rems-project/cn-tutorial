/*@
lemma Append_Nil_R__Seq_Int (datatype Seq_Int L1)
  requires true;
  ensures Append__Seq_Int(L1, Nil__Seq_Int{}) == L1;

lemma Append_Cons_R__Seq_Int (datatype Seq_Int L1, i32 X, datatype Seq_Int L2)
  requires true;
  ensures Append__Seq_Int(L1, Cons__Seq_Int {Head: X, Tail: L2})
          == Append__Seq_Int(Snoc__Seq_Int(L1, X), L2);
@*/
