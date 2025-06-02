// Walks the list and assigns 7 to the value field of every node. (Proof written
// by CPulte and modified by MDD.)

#include "list_preds.h"

// A lemma saying that a list segment followed by a list node can be folded into
// a list segment. This lemma is assumed by CN and must be proved inductively in
// Coq.
// TODO: as of April 2024, CN cannot export such lemmas to Coq because they
// involve resource predicates. Resolving this would require integration with
// Iris or some other Coq resource logic. 
/*@
lemma IntListSeqSnoc(pointer p, pointer tail)
  requires take l1 = IntListSeg(p, tail);
           take v = RW<struct list_node>(tail);
  ensures take l2 = IntListSeg(p, v.next);
          l2 == append(l1, Seq_Cons { val: v.val, next: Seq_Nil {} });
@*/

void list_2(struct list_node *head)
/*@ requires take Xs = IntListSeg(head,NULL);
    ensures take Ys = IntListSeg(head,NULL); @*/
{
  struct list_node *curr;
  curr = head;

  while (curr != 0)
  /*@ inv take Visited = IntListSeg(head,curr);
          take Remaining = IntListSeg(curr,NULL);
          {head}unchanged;
          let prev_curr = curr; @*/
  {
    curr->val = 7;
    curr = curr->next;
    /*@ apply IntListSeqSnoc(head, prev_curr); @*/
  }
  return;
}

