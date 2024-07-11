// TODO - REVISIT

#include "queue_headers.h"
#include "queue_pop_lemma.h"

int IntQueue_pop (struct int_queue *q)
/*@ requires take before = IntQueuePtr(q);
             before != Seq_Nil{};
    ensures take after = IntQueuePtr(q);
            after == tl(before);
            return == hd(before);
@*/
{
  /*@ split_case is_null(q->front); @*/
  struct int_queueCell* h = q->front;
  if (h == q->back) {
    int x = h->first;
    freeIntQueueCell(h);
    q->front = 0;
    q->back = 0;
    /*@ unfold snoc(Seq_Nil{}, x); @*/
    return x;
  } else {
    int x = h->first;
    /*@ apply snoc_facts(h->next, q->back, x); @*/
    q->front = h->next;
    freeIntQueueCell(h);
    return x;
  }
}

int main()
/*@ trusted; @*/
{
}
