#include "list.h"

void free_rec_sllist(struct sllist* l)
// You fill in the rest...
/* --BEGIN-- */
/*@ requires take L = Linked_List_Int(l); @*/
{
  if (l == 0) {
  } else {
    free_rec_sllist(l->tail);
    free_sllist(l);
  }
}
/* --END-- */
