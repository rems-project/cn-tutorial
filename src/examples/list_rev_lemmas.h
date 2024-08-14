/*@
lemma Append_Nil_RList (datatype List L1)
  requires true;
  ensures AppendList(L1, Nil{}) == L1;

lemma Append_Cons_RList (datatype List L1, i32 X, datatype List L2)
  requires true;
  ensures AppendList(L1, Cons {Head: X, Tail: L2})
          == AppendList(SnocList(L1, X), L2);
@*/
