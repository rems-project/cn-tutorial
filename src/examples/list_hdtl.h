/*@
function (i32) Hd (datatype Seq_Int Xs) {
  match Xs {
    Nil__Seq_Int {} => {
      0i32
    }
    Cons__Seq_Int {Head : H, Tail : _} => {
      H
    }
  }
}

function (datatype Seq_Int) Tl (datatype Seq_Int Xs) {
  match Xs {
    Nil__Seq_Int {} => {
      Nil__Seq_Int{}
    }
    Cons__Seq_Int {Head : _, Tail : T} => {
      T
    }
  }
}
@*/
