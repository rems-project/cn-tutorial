// TODO: change i32 to I32
/*@
function [rec] (datatype Seq_Int) Snoc__Seq_Int(datatype Seq_Int Xs, i32 Y) {
  match Xs {
    Nil__Seq_Int {} => {
      Cons__Seq_Int {Head: Y, Tail: Nil__Seq_Int{}}
    }
    Cons__Seq_Int {Head: X, Tail: Zs}  => {
      Cons__Seq_Int{Head: X, Tail: Snoc__Seq_Int (Zs, Y)}
    }
  }
}
@*/
