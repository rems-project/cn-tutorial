#include "list/headers.verif.h"
#include "ref.h"
#include "free.h"

/*@
function [rec] (u32) length(datatype List xs) {
  match xs {
    Nil {} => {
      0u32
    }
    Cons {Head: h, Tail: zs}  => {
      1u32 + length(zs)
    }
  }
}
@*/

void IntList_length_acc_aux (struct sllist *xs, unsigned int *p)
/*@ requires take L1 = SLList_At(xs);
             take P = RW<unsigned int>(p);
    ensures take L1_post = SLList_At(xs);
            take P_post = RW<unsigned int>(p);
            L1 == L1_post;
            P_post == P + length(L1);
@*/
{
  /*@ unfold length(L1); @*/
  if (xs == 0) {
  } else {
    *p = *p + 1;
    IntList_length_acc_aux (xs->tail, p);
  }
}

unsigned int IntList_length_acc (struct sllist *xs)
/*@ requires take Xs = SLList_At(xs);
    ensures take Xs_post = SLList_At(xs);
            Xs == Xs_post;
            return == length(Xs);
@*/
{
  unsigned int *p = refUnsignedInt(0);
  IntList_length_acc_aux(xs, p);
  unsigned int x = *p;
  freeUnsignedInt(p);
  return x;
}
