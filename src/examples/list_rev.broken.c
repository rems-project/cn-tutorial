#include "list.h"

/*@
function [rec] (datatype seq) snoc(datatype seq xs, i32 y) {
  match xs {
    Seq_Nil {} => {
      Seq_Nil {}
    }
    Seq_Cons {head : h, tail : zs}  => {
      snoc (rev(zs), h)
    }
  }
}

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

struct int_list* IntList_rev(struct int_list* xs, int y)
/*@ requires take L1 = IntList(xs) @*/
/*@ ensures take L1_rev = IntList(return) @*/
/*@ ensures L1_rev == rev(L1) @*/
{
  if (xs == 0) {
    return 0;
  } else {

  }
}
