#include "queue_headers.h" 

/*@
lemma assert_not_equal(pointer x, pointer y)
requires
    true;
ensures
    !ptr_eq(x, y);
@*/

void push_induction(struct int_queueCell* front, struct int_queueCell* p)
/*@
  requires
      take Q = IntQueueAux(front, p);
      take P = Owned(p);
      take B = Owned(P.next);
      // Should be derived automatically
      !ptr_eq(front, P.next);
      !is_null(P.next);
  ensures
      take NewQ = IntQueueAux(front, P.next);
      NewQ == snoc(Q, P.first);
      take NewB = Owned(P.next);
      B == NewB;
@*/
{
    if (front == p) {
        /*@ unfold snoc(Q, P.first); @*/
        return;
    } else {
        // Should be derived automatically
        /*@ apply assert_not_equal((*front).next, (*p).next); @*/
        push_induction(front->next, p);
        /*@ unfold snoc(Q, P.first); @*/
        return;
    }
}

