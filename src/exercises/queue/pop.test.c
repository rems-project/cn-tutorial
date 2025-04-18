#include "./headers.test.h"

int pop_queue (struct queue *q)
/* --BEGIN-- */
/*@ requires take Q = QueuePtr_At(q);
             Q != Nil{};
    ensures take Q_post = QueuePtr_At(q);
            Q_post == Tl(Q);
            return == Hd(Q);
@*/
/* --END-- */
{
  struct queue_cell* h = q->front;
  if (h == q->back) {
    int x = h->first;
    free__queue_cell(h);
    q->front = 0;
    q->back = 0;
    return x;
  } else {
    int x = h->first;
    q->front = h->next;
    free__queue_cell(h);
    return x;
  }
}
