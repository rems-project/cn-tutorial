#include "list.h"

void free_rec_list_int(struct list_int* l)
// You fill in the rest...
/* --BEGIN-- */
/*@ requires take L = Linked_List_Int(l); @*/
{
  if (l == 0) {
  } else {
    free_rec_list_int(l->tail);
    free_list_int(l);
  }
}
/* --END-- */
