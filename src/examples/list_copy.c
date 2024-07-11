// TODO - REVISIT

#include "list.h"

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

int main()
/*@ trusted; @*/
{

}
