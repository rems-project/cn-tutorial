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
