#include "queue_headers.h"

int IntQueue_pop (struct int_queue *q)
{
  struct int_queueCell* h = q->front;
  struct int_queueCell* t = q->back;
  if (h == t) {
    int x = h->first;
    freeIntQueueCell(h);
    q->front = 0;
    q->back = 0;
    return x;
  } else {
    int x = h->first;
    struct int_queueCell* n = h->next;
    q->front = n;
    freeIntQueueCell(h);
    return x;
  }
}

