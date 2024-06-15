#include "queue_headers.h" 

void IntQueue_push (int x, struct int_queue *q)
{
  struct int_queueCell *c = mallocIntQueueCell();
  c->first = x;
  c->next = 0;
  if (q->back == 0) {
    q->front = c;
    q->back = c;
    return;
  } else {
    q->back->next = c;
    q->back = c;
    return;
  }
}
