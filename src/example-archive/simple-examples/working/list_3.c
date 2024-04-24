// Reverse a list. Compare with:
// https://github.com/rems-project/cerberus/blob/master/tests/cn/list_rev01.c

#include "list_preds.h"

struct list_node *list_reverse_1(struct list_node *head)
/*@ requires take ListPre  = IntListSeg(head, NULL) @*/
/*@ ensures  take ListPost = IntListSeg(return, NULL) @*/
{
  struct list_node *prev, *next, *curr;
  curr = head;

  prev = 0;
  next = 0; // TODO: Shouldn't be needed  Note that this is also
            // called out as a FIXME in the CN repo version

  while (curr != 0)
  /*@ inv take InInv = IntListSeg(curr, NULL);
          take RevInv = IntListSeg(prev, NULL) @*/
  {
    next = curr->next;
    curr->next = prev;
    prev = curr;
    curr = next;
  }
  return prev;
}

