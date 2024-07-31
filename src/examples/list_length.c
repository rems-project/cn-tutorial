/* list_length.c */
// TODO: u32 to U32
#include "list.h"

/* --BEGIN-- */
/*@
function [rec] (u32) Length__Seq_Int(datatype Seq_Int Xs) {
  match Xs {
    Nil__Seq_Int {} => {
      0u32
    }
    Cons__Seq_Int {Head : H, Tail : Zs}  => {
      1u32 + Length__Seq_Int(Zs)
    }
  }
}
@*/

/* --END-- */
unsigned int length__list_int (struct list_int *xs)
/* --BEGIN-- */
/*@ requires take L1 = Linked_List_Int(xs);
    ensures take L1_ = Linked_List_Int(xs);
            L1 == L1_;
            return == Length__Seq_Int(L1);
@*/
/* --END-- */
{
  if (xs == 0) {
/* --BEGIN-- */
    /*@ unfold Length__Seq_Int(L1); @*/
/* --END-- */
    return 0;
  } else {
/* --BEGIN-- */
    /*@ unfold Length__Seq_Int(L1); @*/
/* --END-- */
    return 1 + length__list_int(xs->tail);
  }
}
