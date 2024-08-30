#include "queue_headers.h" 

void IntQueue_push (int x, struct queue *q)
{
  struct queue_cell *c = mallocIntqueue_cell();
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
