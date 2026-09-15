// Reverse a list. Compare with:
// https://github.com/rems-project/cerberus/blob/master/tests/cn/list_rev01.c

#include "list_preds.h"

struct list_node *list_reverse_1(struct list_node *head)
/*@ requires take ListPre  = IntListSeg(head, NULL);
    ensures  take ListPost = IntListSeg(return, NULL); @*/
{
  struct list_node *prev, *next, *curr;
  curr = head;

  prev = 0;
  next = 0; // TODO: Shouldn't be needed  Note that this is also
            // called out as a FIXME in the CN repo version

  while (curr != 0)
  /*@ inv take InInv = IntListSeg(curr, NULL);
          take RevInv = IntListSeg(prev, NULL); @*/
  {
    next = curr->next;
    curr->next = prev;
    prev = curr;
    curr = next;
  }
  return prev;
}


void *cn_malloc(unsigned long size);

int main(void)
/*@ trusted; @*/
{
  // Constructs list with values [2, 4, 6]
  struct list_node *n3 = cn_malloc(sizeof(struct list_node));
  n3->val = 6;
  n3->next = 0;
  struct list_node *n2 = cn_malloc(sizeof(struct list_node));
  n2->val = 4;
  n2->next = n3;
  struct list_node *n1 = cn_malloc(sizeof(struct list_node));
  n1->val = 2;
  n1->next = n2;
  list_reverse_1(n1);
}