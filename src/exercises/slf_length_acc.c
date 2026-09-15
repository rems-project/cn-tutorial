#include "list/headers.verif.h"
#include "ref.h"
#include "free.h"

/*@
function [rec] (integer) length(datatype List xs) {
  match xs {
    Nil {} => {
      0
    }
    Cons {Head: h, Tail: zs}  => {
      1 + length(zs)
    }
  }
}
@*/

void IntList_length_acc_aux (struct sllist *xs, unsigned int *p)
/* --BEGIN-- */
/*@ requires take L1 = SLList_At(xs);
             take P = RW<unsigned int>(p);
	     P + length(L1) <= MAXu32();
    ensures take L1_post = SLList_At(xs);
            take P_post = RW<unsigned int>(p);
            L1 == L1_post;
            P_post == P + length(L1);
@*/
/* --END-- */
{
/* --BEGIN-- */
  /*@ unfold length(L1); @*/
/* --END-- */
  if (xs == 0) {
  } else {
    *p = *p + 1;
    IntList_length_acc_aux (xs->tail, p);
  }
}

unsigned int IntList_length_acc (struct sllist *xs)
/* --BEGIN-- */
/*@ requires take Xs = SLList_At(xs);
             length(Xs) <= MAXu32();
    ensures take Xs_post = SLList_At(xs);
            Xs == Xs_post;
            return == length(Xs);
@*/
/* --END-- */
{
  unsigned int *p = refUnsignedInt(0);
  IntList_length_acc_aux(xs, p);
  unsigned int x = *p;
  free__unsigned_int(p);
  return x;
}
