#include "list_snoc.h"

/*@
function [rec] (datatype Seq_Int) Rev__Seq_Int(datatype Seq_Int Xs) {
  match Xs {
    Nil__Seq_Int {} => {
      Nil__Seq_Int {}
    }
    Cons__Seq_Int {Head : H, Tail : Zs}  => {
      Snoc__Seq_Int (Rev__Seq_Int(Zs), H)
    }
  }
}
@*/
