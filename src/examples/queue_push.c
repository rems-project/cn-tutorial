#include "queue_headers.h" 
#include "queue_push_lemma.h" 

void IntQueue_push (int x, struct int_queue *q)
/*@ requires take Q = IntQueuePtr(q);
    ensures take Q_post = IntQueuePtr(q);
            Q_post == Snoc (Q, x);
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
    /*@ apply push_lemma (q->front, oldback); @*/
    return;
  }
}
