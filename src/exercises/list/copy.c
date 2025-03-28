#include "./headers.verif.h"

struct sllist* slcopy (struct sllist *l)
/*@ requires take L = SLList_At(l);
    ensures take L_post = SLList_At(l);
            take Ret = SLList_At(return);
            L == L_post;
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
