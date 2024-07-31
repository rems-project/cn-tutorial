/* list_length.c */
// TODO: u32 to U32
#include "list.h"

/* --BEGIN-- */
/*@
function [rec] (u32) Length__Seq_Int(datatype Seq_Int L) {
  match L {
    Nil__Seq_Int {} => {
      0u32
    }
    Cons__Seq_Int {Head : H, Tail : T}  => {
      1u32 + Length__Seq_Int(T)
    }
  }
}
@*/

/* --END-- */
unsigned int length__list_int (struct list_int *l)
/* --BEGIN-- */
/*@ requires take L = Linked_List_Int(l);
    ensures take L_ = Linked_List_Int(l);
            L == L_;
            return == Length__Seq_Int(L);
@*/
/* --END-- */
{
  if (l == 0) {
/* --BEGIN-- */
    /*@ unfold Length__Seq_Int(L); @*/
/* --END-- */
    return 0;
  } else {
/* --BEGIN-- */
    /*@ unfold Length__Seq_Int(L); @*/
/* --END-- */
    return 1 + length__list_int(l->tail);
  }
}
