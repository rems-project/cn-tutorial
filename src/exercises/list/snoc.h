/*@
function [rec] (datatype List) Snoc(datatype List Xs, integer Y) {
  match Xs {
    Nil {} => {
      Cons {Head: Y, Tail: Nil{}}
    }
    Cons {Head: X, Tail: Zs}  => {
      Cons{Head: X, Tail: Snoc (Zs, Y)}
    }
  }
}
@*/
