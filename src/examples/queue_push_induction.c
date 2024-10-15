#include "queue_headers.h" 

void push_induction(struct int_queueCell* front
        , struct int_queueCell* second_last
        , struct int_queueCell* last)
/*@
  requires
      ptr_eq(front, second_last) || !addr_eq(front, second_last);
      take Q = IntQueueAux(front, second_last);
      take Second_last = Owned(second_last);
      ptr_eq(Second_last.next, last);
      take Last = Owned(last);
  ensures
      ptr_eq(front, last) || !addr_eq(front, last);
      take NewQ = IntQueueAux(front, last);
      take Last2 = Owned(last);
      NewQ == snoc(Q, Second_last.first);
      Last == Last2;
@*/
{
    if (front == second_last) {
        /*@ unfold snoc(Q, Second_last.first); @*/
        return;
    } else {
        push_induction(front->next, second_last, last);
        /*@ unfold snoc(Q, Second_last.first); @*/
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
    push_induction(q->front, oldback, c);
    return;
  }
}
