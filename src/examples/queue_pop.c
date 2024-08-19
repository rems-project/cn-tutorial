#include "queue_headers.h"
#include "queue_pop_lemma.h"

int IntQueue_pop (struct int_queue *q)
/*@ requires take Q = IntQueuePtr(q);
             Q != Nil{};
    ensures take Q_post = IntQueuePtr(q);
            Q_post == Tl(Q);
            return == Hd(Q);
@*/
{
  /*@ split_case is_null(q->front); @*/
  struct int_queueCell* h = q->front;
  if (h == q->back) {
    int x = h->first;
    freeIntQueueCell(h);
    q->front = 0;
    q->back = 0;
    /*@ unfold Snoc(Nil{}, x); @*/
    return x;
  } else {
    int x = h->first;
    /*@ apply snoc_facts(h->next, q->back, x); @*/
    q->front = h->next;
    freeIntQueueCell(h);
    return x;
  }
}
