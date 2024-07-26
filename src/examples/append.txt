#include "list.h"
#include "list_append.h"

// TODO REVISIT

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

int main()
/*@ trusted; @*/
{
    struct int_list num3 = { .head = 3, .tail = 0 };
    struct int_list num2 = { .head = 2, .tail = &num3 };
    struct int_list num1 = { .head = 1, .tail = &num2 };

    struct int_list ys = { .head = 4, .tail = 0 };

    struct int_list *res1 = IntList_append(0, &ys);

    struct int_list *res2 = IntList_append(&num1, &ys);
}
