// append.h

/*@
function (datatype seq) append_hack(datatype seq xs, datatype seq ys) {
  ys
}
  
function (datatype seq) append(datatype seq xs, datatype seq ys) {
  match xs {
    Seq_Nil {} => {
      ys
    }
    Seq_Cons {head : h, tail : zs}  => {
      Seq_Cons {head: h, tail: append_hack(zs, ys)}
    }
  }
}
@*/
