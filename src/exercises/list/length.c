#include "./headers.h"

/* --BEGIN-- */
/*@
function [rec] (u32) Length(datatype List L) {
  match L {
    Nil {} => {
      0u32
    }
    Cons {Head: H, Tail : T}  => {
      1u32 + Length(T)
    }
  }
}
@*/

/* --END-- */
unsigned int length (struct sllist *l)
/* --BEGIN-- */
/*@ requires take L = SLList_At(l);
    ensures take L_post = SLList_At(l);
            L == L_post;
            return == Length(L);
@*/
/* --END-- */
{
  if (l == 0) {
/* --BEGIN-- */
    /*@ unfold Length(L); @*/
/* --END-- */
    return 0;
  } else {
/* --BEGIN-- */
    /*@ unfold Length(L); @*/
/* --END-- */
    return 1 + length(l->tail);
  }
}
