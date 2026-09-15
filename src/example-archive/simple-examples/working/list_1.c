// A function on lists that does nothing. Note we don't need an inductive lemma
// here because the precondition is preserved by the frame rule.

#include "list_preds.h"

struct list_node *list_1(struct list_node *xs)
/*@ requires take Xs = IntListSeg(xs,NULL);
    ensures 
      take Ys = IntListSeg(return,NULL); 
      Ys == Xs; @*/
{
  struct list_node *ys;
  ys = xs;
  return ys;
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
  list_1(n1);
}