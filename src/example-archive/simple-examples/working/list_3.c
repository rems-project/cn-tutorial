// The same code as list_2.c, but the proof establishes that every node in the
// list is rewritten to the value 7. 

#include "list_preds.h"

// This version of the predicate takes an i32 argument. Every node in the list
// must store this value. 

/*@
predicate [rec] (datatype seq) IntListSegVal(pointer p, pointer tail, i32 tval) {
  if (addr_eq(p,tail)) {
    return Seq_Nil{};
  } else {
    take H = RW<struct list_node>(p);
    assert (is_null(H.next) || H.next != NULL);
    assert (H.val == tval); 
    take tl = IntListSeg(H.next, tail);
    return (Seq_Cons { val: H.val, next: tl });
  }
}
@*/
/*@
lemma IntListSeqSnocVal(pointer p, pointer tail, i32 tval)
  requires take l1 = IntListSegVal(p, tail, tval);
           take v = RW<struct list_node>(tail);
           v.val == tval; 
  ensures take l2 = IntListSegVal(p, v.next, tval);
          l2 == append(l1, Seq_Cons { val: v.val, next: Seq_Nil {} }); 
@*/


void list_3(struct list_node *head)
/*@ requires take Xs = IntListSeg(head,NULL);
    ensures  take Ys = IntListSegVal(head,NULL,7i32); @*/
{
  struct list_node *curr;
  curr = head;

  while (curr != 0)
  /*@ inv take Visited = IntListSegVal(head,curr,7i32);
          take Remaining = IntListSeg(curr,NULL);
          {head}unchanged;
          let i_curr = curr; 
          @*/
  {
    curr->val = 7;
    curr = curr->next;
    /*@ apply IntListSeqSnocVal(head, i_curr, 7i32); @*/
  }
  return;
}
