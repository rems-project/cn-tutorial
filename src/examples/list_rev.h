#include "list_snoc_spec.h"

/*@
function [rec] (datatype seq) rev(datatype seq xs) {
  match xs {
    Seq_Nil {} => {
      Seq_Nil {}
    }
    Seq_Cons {head : h, tail : zs}  => {
      snoc (rev(zs), h)
    }
  }
}
@*/
