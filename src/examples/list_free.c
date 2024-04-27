#include "list.h"

void IntList_free_list(struct int_list* xs)
// You fill in the rest...
/* --BEGIN-- */
/*@ requires take L1 = IntList(xs); @*/
{
  if (xs == 0) {
  } else {
    IntList_free_list(xs->tail);
    freeIntList(xs);
  }
}
/* --END-- */
