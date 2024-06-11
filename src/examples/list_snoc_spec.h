/*@
function (datatype seq) snoc_hack(datatype seq xs, i32 y) {
Seq_Cons {head: y, tail: Seq_Nil{}}
}

function (datatype seq) snoc(datatype seq xs, i32 y) {
  match xs {
    Seq_Nil {} => {
      Seq_Cons {head: y, tail: Seq_Nil{}}
    }
    Seq_Cons {head: x, tail: zs}  => {
      Seq_Cons{head: x, tail: snoc_hack (zs, y)}
    }
  }
}
@*/
