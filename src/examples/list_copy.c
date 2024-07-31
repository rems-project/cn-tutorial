#include "list.h"

struct list_int* list_int_copy (struct list_int *l)
/*@ requires take L = Linked_List_Int(l);
    ensures take L_ = Linked_List_Int(l);
            take Ret = Linked_List_Int(return);
            L == L_;
            L == Ret;
@*/
{
  if (l == 0) {
    return nil__list_int();
  } else {
    struct list_int *new_tail = list_int_copy(l->tail);
    return cons__list_int(l->head, new_tail);
  }
}
