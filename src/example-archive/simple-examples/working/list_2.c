// Walks the list and assigns 7 to the value field of every node. (Proof written
// by CPulte and modified by MDD.)

#include "list_preds.h"

void list_2(struct list_node *head)
/*@ requires take Xs = IntListSeg(head,NULL) @*/
/*@ ensures take Ys = IntListSeg(head,NULL) @*/
{
  struct list_node *curr;
  curr = head;

  while (curr != 0)
  /*@ inv take Visited = IntListSeg(head,curr);
          take Remaining = IntListSeg(curr,NULL);
          {head}unchanged;
          let prev_curr = curr @*/
  {
    curr->val = 7;
    curr = curr->next;
    /*@ apply IntListSeqSnocVal(head, prev_curr); @*/
  }
  return;
}

// Stronger version of the proof that establishes the list is written to all 7s 

// TODO before merge - prove that the resulting list is all-7s 

void list_2_alt(struct list_node *head)
/*@ requires take Xs = IntListSeg(head,NULL) @*/
/*@ ensures  take Ys = IntListSeg(head,NULL) @*/
{
  struct list_node *curr;
  curr = head;

  while (curr != 0)
  /*@ inv take Visited = IntListSeg(head,curr);
          take Remaining = IntListSeg(curr,NULL);
          {head}unchanged;
          let i_curr = curr; 
          each 
          @*/
  {
    curr->val = 7;
    curr = curr->next;
    /*@ apply IntListSeqSnocVal(head, i_curr); @*/
  }
  return;
}
