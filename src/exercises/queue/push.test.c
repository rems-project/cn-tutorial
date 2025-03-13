#include "./headers.test.h"

void push_queue (int x, struct queue *q)
/* --BEGIN-- */
/*@ requires take Q = QueuePtr_At(q);
    ensures take Q_post = QueuePtr_At(q);
            Q_post == Snoc (Q, x);
@*/
/* --END-- */
{
  struct queue_cell *c = malloc_queue_cell();
  c->first = x;
  c->next = 0;
  if (q->back == 0) {
    q->front = c;
    q->back = c;
    return;
  } else {
    struct queue_cell *oldback = q->back;
    q->back->next = c;
    q->back = c;
    return;
  }
}
