#include "list.h"
#include "append.h"

struct int_list* IntList_copy (struct int_list *xs)
/*@ requires take L1 = IntList(xs)
    ensures take L1_ = IntList(xs);
            take L2 = IntList(return);
            L1 == L1_;
            L1 == L2
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
/*@ requires take L1 = IntList(xs) @*/
/*@ requires take L2 = IntList(ys) @*/
/*@ ensures take L1_ = IntList(xs) @*/
/*@ ensures take L2_ = IntList(ys) @*/
/*@ ensures take L3 = IntList(return) @*/
/*@ ensures L3 == append(L1, L2) @*/
/*@ ensures L1 == L1_ @*/
/*@ ensures L2 == L2_ @*/
{
  if (xs == 0) {
    /*@ unfold append(L1, L2); @*/
    return IntList_copy(ys);
  } else {
    /*@ unfold append(L1, L2); @*/
    struct int_list *new_tail = IntList_append2(xs->tail, ys);
    return IntList_cons(xs->head, new_tail);
  }
}

// Note that it would not make sense to do the usual
// functional-programming trick of copying xs but sharing ys.  (Why?)
