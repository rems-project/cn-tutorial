// append.h

/*@
function [rec] (datatype List) AppendList(datatype List L1, datatype List L2) {
  match L1 {
    Nil {} => {
      L2
    }
    Cons {Head : H, Tail : T}  => {
      Cons {Head: H, Tail: AppendList(T, L2)}
    }
  }
}
@*/
