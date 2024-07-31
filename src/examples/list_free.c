#include "list.h"

void free_rec_list_int(struct list_int* xs)
// You fill in the rest...
/* --BEGIN-- */
/*@ requires take L1 = Linked_List_Int(xs); @*/
{
  if (xs == 0) {
  } else {
    free_rec_list_int(xs->tail);
    free_list_int(xs);
  }
}
/* --END-- */
