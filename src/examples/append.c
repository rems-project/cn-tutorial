#include "list.h"
#include "list_append.h"

struct sllist* IntList_append(struct sllist* xs, struct sllist* ys)
/*@ requires take L1 = SLList(xs); @*/
/*@ requires take L2 = SLList(ys); @*/
/*@ ensures take L3 = SLList(return); @*/
/*@ ensures L3 == Append(L1, L2); @*/
{
  if (xs == 0) {
    /*@ unfold Append(L1, L2); @*/
    return ys;
  } else {
    /*@ unfold Append(L1, L2); @*/
    struct sllist *new_tail = IntList_append(xs->tail, ys);
    xs->tail = new_tail;
    return xs;
  }
}
