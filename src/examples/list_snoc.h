/*@
function [rec] (datatype seq) snoc(datatype seq xs, i32 y) {
  match xs {
    Seq_Nil {} => {
      Seq_Cons {head: y, tail: Seq_Nil{}}
    }
    Seq_Cons {head: x, tail: zs}  => {
      Seq_Cons{head: x, tail: snoc (zs, y)}
    }
  }
}
@*/
