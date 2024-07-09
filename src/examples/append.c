#include "list.h"
#include "list_append.h"

struct int_list* IntList_append(struct int_list* xs, struct int_list* ys)
/*@ requires take L1 = IntList(xs); @*/
/*@ requires take L2 = IntList(ys); @*/
/*@ ensures take L3 = IntList(return); @*/
/*@ ensures L3 == append(L1, L2); @*/
{
  if (xs == 0) {
    /*@ unfold append(L1, L2); @*/
    return ys;
  } else {
    /*@ unfold append(L1, L2); @*/
    struct int_list *new_tail = IntList_append(xs->tail, ys);
    xs->tail = new_tail;
    return xs;
  }
}
