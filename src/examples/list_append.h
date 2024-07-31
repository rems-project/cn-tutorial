// append.h

/*@
function [rec] (datatype Seq_Int) Append__Seq_Int(datatype Seq_Int Xs, datatype Seq_Int Ys) {
  match Xs {
    Nil__Seq_Int {} => {
      Ys
    }
    Cons__Seq_Int {Head : H, Tail : Zs}  => {
      Cons__Seq_Int {Head: H, Tail: Append__Seq_Int(Zs, Ys)}
    }
  }
}
@*/
