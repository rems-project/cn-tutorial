#include "./headers.test.h"
#include "./append.h"

struct sllist* IntList_append(struct sllist* xs, struct sllist* ys)
/*@ requires take L1 = SLList_At(xs);
             take L2 = SLList_At(ys); 
    ensures take L3 = SLList_At(return);
            L3 == Append(L1, L2); @*/
{
  if (xs == 0) {
    return ys;
  } else {
    struct sllist *new_tail = IntList_append(xs->tail, ys);
    xs->tail = new_tail;
    return xs;
  }
}
