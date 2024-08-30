#include "queue_headers.h"

int IntQueue_pop (struct queue *q)
{
  struct queue_cell* h = q->front;
  if (h == q->back) {
    int x = h->first;
    freeIntqueue_cell(h);
    q->front = 0;
    q->back = 0;
    return x;
  } else {
    int x = h->first;
    q->front = h->next;
    freeIntqueue_cell(h);
    return x;
  }
}
