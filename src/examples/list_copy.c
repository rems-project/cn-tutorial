#include "list.h"

struct sllist* slcopy (struct sllist *l)
/*@ requires take L = SLList(l);
    ensures take L_ = SLList(l);
            take Ret = SLList(return);
            L == L_;
            L == Ret;
@*/
{
  if (l == 0) {
    return slnil();
  } else {
    struct sllist *new_tail = slcopy(l->tail);
    return slcons(l->head, new_tail);
  }
}
