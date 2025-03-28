#include "./headers.test.h"
#include "./append.h"

struct sllist* IntList_copy (struct sllist *xs)
/*@ requires take Xs = SLList_At(xs);
    ensures take Xs_post = SLList_At(xs);
            take R = SLList_At(return);
            Xs == Xs_post;
            Xs == R;
@*/
{
  if (xs == 0) {
    return slnil();
  } else {
    struct sllist *new_tail = IntList_copy(xs->tail);
    return slcons(xs->head, new_tail);
  }
}

struct sllist* IntList_append2 (struct sllist *xs, struct sllist *ys)
/* --BEGIN-- */
/*@ requires take Xs = SLList_At(xs);
             take Ys = SLList_At(ys);
    ensures take Xs_post = SLList_At(xs);
            take Ys_post = SLList_At(ys);
            take Ret = SLList_At(return);
            Ret == Append(Xs, Ys);
            Xs == Xs_post;
            Ys == Ys_post; @*/
/* --END-- */
{
  if (xs == 0) {
    return IntList_copy(ys);
  } else {
    struct sllist *new_tail = IntList_append2(xs->tail, ys);
    return slcons(xs->head, new_tail);
  }
}
