#include "./headers.verif.h"
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
/*@ requires take Xs = SLList_At(xs); @*/
/*@ requires take Ys = SLList_At(ys); @*/
/*@ ensures take Xs_post = SLList_At(xs); @*/
/*@ ensures take Ys_post = SLList_At(ys); @*/
/*@ ensures take Ret = SLList_At(return); @*/
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
