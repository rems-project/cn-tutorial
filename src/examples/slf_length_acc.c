// TODO - REVISIT

#include "list.h"
#include "ref.h"
#include "free.h"

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

void IntList_length_acc_aux (struct int_list *xs, unsigned int *p)
/*@ requires take L1 = IntList(xs);
             take n = Owned<unsigned int>(p);
    ensures take L1_ = IntList(xs);
            take n_ = Owned<unsigned int>(p);
            L1 == L1_;
            n_ == n + length(L1);
@*/
{
  /*@ unfold length(L1); @*/
  if (xs == 0) {
  } else {
    *p = *p + 1;
    IntList_length_acc_aux (xs->tail, p);
  }
}

unsigned int IntList_length_acc (struct int_list *xs)
/*@ requires take L1 = IntList(xs);
    ensures take L1_ = IntList(xs);
            L1 == L1_;
            return == length(L1);
@*/
{
  unsigned int *p = refUnsignedInt(0);
  IntList_length_acc_aux(xs, p);
  unsigned int x = *p;
  freeUnsignedInt(p);
  return x;
}

int main()
/*@ trusted; @*/
{
}
