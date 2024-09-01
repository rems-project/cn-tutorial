#include "list.h"

void free__rec_sllist(struct sllist* l)
// You fill in the rest...
/* --BEGIN-- */
/*@ requires take L = SLList_At(l); @*/
{
  if (l == 0) {
  } else {
    free__rec_sllist(l->tail);
    free__sllist(l);
  }
}
/* --END-- */
