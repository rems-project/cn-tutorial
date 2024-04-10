#include "list.h"

// BCP: Should really #include this from bcp_length.c, not repeat it!

/* --BEGIN-- */
/*@
function [rec] (u32) length(datatype seq xs) {
  match xs {
    Seq_Nil {} => {
      0u32
    }
    Seq_Cons {head : h, tail : zs}  => {
      1u32 + length(zs)
    }
  }
}
@*/

/* --END-- */
unsigned int IntList_length (struct int_list *xs)
/* --BEGIN-- */
/*@ requires take L1 = IntList(xs)
    ensures take L1_ = IntList(xs);
            L1 == L1_;
            return == length(L1)
@*/
/* --END-- */
{
  if (xs == 0) {
/* --BEGIN-- */
    /*@ unfold length(L1); @*/
/* --END-- */
    return 0;
  } else {
/* --BEGIN-- */
    /*@ unfold length(L1); @*/
/* --END-- */
    return 1 + IntList_length (xs->tail);
  }
}


struct sized_stack {
  unsigned int size;
  struct int_list* data;
};

/*@
datatype sizeAndData {
  SD {u32 s, datatype seq d}
}

predicate (datatype sizeAndData) SizedStack(pointer p) {
    take S = Owned<struct sized_stack>(p);
    let s = S.size;
    take d = IntList(S.data);
    return (SD { s: s, d: d });
}
@*/
