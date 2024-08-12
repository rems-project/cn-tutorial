#include "list.h"

struct sllist* sllist_copy (struct sllist *l)
/*@ requires take L = Linked_List_Int(l);
    ensures take L_ = Linked_List_Int(l);
            take Ret = Linked_List_Int(return);
            L == L_;
            L == Ret;
@*/
{
  if (l == 0) {
    return nil__sllist();
  } else {
    struct sllist *new_tail = sllist_copy(l->tail);
    return cons__sllist(l->head, new_tail);
  }
}
