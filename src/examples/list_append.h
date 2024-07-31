// append.h

/*@
function [rec] (datatype Seq_Int) Append__Seq_Int(datatype Seq_Int L1, datatype Seq_Int L2) {
  match L1 {
    Nil__Seq_Int {} => {
      L2
    }
    Cons__Seq_Int {Head : H, Tail : T}  => {
      Cons__Seq_Int {Head: H, Tail: Append__Seq_Int(T, L2)}
    }
  }
}
@*/
