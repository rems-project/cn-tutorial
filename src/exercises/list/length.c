#include "./headers.verif.h"

/* --BEGIN-- */
/*@
function [rec] (integer) Length(datatype List L) {
  match L {
    Nil {} => {
      0
    }
    Cons {Head: H, Tail : T}  => {
      1 + Length(T)
    }
  }
}
@*/

/* --END-- */
unsigned int length (struct sllist *l)
/* --BEGIN-- */
/*@ requires take L = SLList_At(l);
             Length(L) < MAXu32();
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
