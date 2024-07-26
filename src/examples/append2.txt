#include "list.h"
#include "list_append.h"

struct int_list* IntList_copy (struct int_list *xs)
/*@ requires take L1 = IntList(xs);
    ensures take L1_ = IntList(xs);
            take L2 = IntList(return);
            L1 == L1_;
            L1 == L2;
@*/
{
  if (xs == 0) {
    return IntList_nil();
  } else {
    struct int_list *new_tail = IntList_copy(xs->tail);
    return IntList_cons(xs->head, new_tail);
  }
}

struct int_list* IntList_append2 (struct int_list *xs, struct int_list *ys)
/* --BEGIN-- */
/*@ requires take L1 = IntList(xs); @*/
/*@ requires take L2 = IntList(ys); @*/
/*@ ensures take L1_ = IntList(xs); @*/
/*@ ensures take L2_ = IntList(ys); @*/
/*@ ensures take L3 = IntList(return); @*/
/*@ ensures L3 == append(L1, L2); @*/
/*@ ensures L1 == L1_; @*/
/*@ ensures L2 == L2_; @*/
/* --END-- */
{
  if (xs == 0) {
/* --BEGIN-- */
    /*@ unfold append(L1, L2); @*/
/* --END-- */
    return IntList_copy(ys);
  } else {
/* --BEGIN-- */
    /*@ unfold append(L1, L2); @*/
/* --END-- */
    struct int_list *new_tail = IntList_append2(xs->tail, ys);
    return IntList_cons(xs->head, new_tail);
  }
}
