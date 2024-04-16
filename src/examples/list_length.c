/* list_length.c */

#include "list.h"

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
