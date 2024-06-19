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
      !ptr_eq(front, P.next);
      !is_null(P.next);
  ensures
      take NewQ = IntQueueAux(front, P.next);
      NewQ == snoc(Q, P.first);
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

void IntQueue_push (int x, struct int_queue *q)
/*@ requires take before = IntQueuePtr(q);
    ensures take after = IntQueuePtr(q);
            after == snoc (before, x);
@*/
{
  struct int_queueCell *c = mallocIntQueueCell();
  /*@ apply assert_not_equal((*q).front, c); @*/
  c->first = x;
  c->next = 0;
  if (q->back == 0) {
    q->front = c;
    q->back = c;
    return;
  } else {
    struct int_queueCell *oldback = q->back;
    q->back->next = c;
    q->back = c;
    push_induction(q->front, oldback);
    return;
  }
}
