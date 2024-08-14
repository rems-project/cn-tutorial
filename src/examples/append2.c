#include "list.h"
#include "list_append.h"

struct sllist* IntList_copy (struct sllist *xs)
/*@ requires take L1 = SLList(xs);
    ensures take L1_ = SLList(xs);
            take L2 = SLList(return);
            L1 == L1_;
            L1 == L2;
@*/
{
  if (xs == 0) {
    return slnil();
  } else {
    struct sllist *new_tail = IntList_copy(xs->tail);
    return slcons(xs->head, new_tail);
  }
}

struct sllist* IntList_append2 (struct sllist *xs, struct sllist *ys)
/* --BEGIN-- */
/*@ requires take L1 = SLList(xs); @*/
/*@ requires take L2 = SLList(ys); @*/
/*@ ensures take L1_ = SLList(xs); @*/
/*@ ensures take L2_ = SLList(ys); @*/
/*@ ensures take L3 = SLList(return); @*/
/*@ ensures L3 == Append(L1, L2); @*/
/*@ ensures L1 == L1_; @*/
/*@ ensures L2 == L2_; @*/
/* --END-- */
{
  if (xs == 0) {
/* --BEGIN-- */
    /*@ unfold Append(L1, L2); @*/
/* --END-- */
    return IntList_copy(ys);
  } else {
/* --BEGIN-- */
    /*@ unfold Append(L1, L2); @*/
/* --END-- */
    struct sllist *new_tail = IntList_append2(xs->tail, ys);
    return slcons(xs->head, new_tail);
  }
}
