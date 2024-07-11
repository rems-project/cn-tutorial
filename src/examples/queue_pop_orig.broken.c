// TODO - REVISIT

#include "queue_headers.h"

int IntQueue_pop (struct int_queue *q)
{
  struct int_queueCell* h = q->front;
  if (h == q->back) {
    int x = h->first;
    freeIntQueueCell(h);
    q->front = 0;
    q->back = 0;
    return x;
  } else {
    int x = h->first;
    q->front = h->next;
    freeIntQueueCell(h);
    return x;
  }
}

int main()
/*@ trusted; @*/
{
}
