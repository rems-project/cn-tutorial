#include "list.h"

struct list_int* list_int_copy (struct list_int *xs)
/*@ requires take L1 = Linked_List_Int(xs);
    ensures take L1_ = Linked_List_Int(xs);
            take L2 = Linked_List_Int(return);
            L1 == L1_;
            L1 == L2;
@*/
{
  if (xs == 0) {
    return nil__list_int();
  } else {
    struct list_int *new_tail = list_int_copy(xs->tail);
    return cons__list_int(xs->head, new_tail);
  }
}
