// TODO: change i32 to I32
/*@
function [rec] (datatype List) SnocList(datatype List Xs, i32 Y) {
  match Xs {
    Nil {} => {
      Cons {Head: Y, Tail: Nil{}}
    }
    Cons {Head: X, Tail: Zs}  => {
      Cons{Head: X, Tail: SnocList (Zs, Y)}
    }
  }
}
@*/
