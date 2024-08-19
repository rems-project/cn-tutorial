#include "list.h"
#include "list_append.h"

struct sllist* IntList_copy (struct sllist *xs)
/*@ requires take Xs = SLList(xs);
    ensures take Xs_post = SLList(xs);
            take R = SLList(return);
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
/*@ requires take Xs = SLList(xs); @*/
/*@ requires take Ys = SLList(ys); @*/
/*@ ensures take Xs_post = SLList(xs); @*/
/*@ ensures take Ys_post = SLList(ys); @*/
/*@ ensures take Ret = SLList(return); @*/
/*@ ensures Ret == Append(Xs, Ys); @*/
/*@ ensures Xs == Xs_post; @*/
/*@ ensures Ys == Ys_post; @*/
/* --END-- */
{
  if (xs == 0) {
/* --BEGIN-- */
    /*@ unfold Append(Xs, Ys); @*/
/* --END-- */
    return IntList_copy(ys);
  } else {
/* --BEGIN-- */
    /*@ unfold Append(Xs, Ys); @*/
/* --END-- */
    struct sllist *new_tail = IntList_append2(xs->tail, ys);
    return slcons(xs->head, new_tail);
  }
}
