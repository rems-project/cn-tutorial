#include "queue_headers.h" 

/*@
lemma aux_induction(pointer front, pointer prev, pointer back, 
                    datatype seq before, i32 prev_pushed)
requires
    take Prev = Owned<struct int_queueCell>(prev);
    take Q = IntQueueAux(front, prev);
    ptr_eq(Prev.next, back);                  // sanity check
    Prev.first == prev_pushed;                // sanity check
    snoc(Q, prev_pushed) == before;           // sanity check
ensures
    take Q2 = IntQueueAux(front, back);
    before == Q2;
@*/

void IntQueue_push (int x, struct int_queue *q)
/*@ requires take before = IntQueuePtr(q);
    ensures take after = IntQueuePtr(q);
            after == snoc (before, x);
@*/
{
  struct int_queueCell *c = mallocIntQueueCell();
  c->first = x;
  c->next = 0;
  if (q->back == 0) {
    /*@ assert (before == Seq_Nil{}); @*/
    q->front = c;
    q->back = c;
    return;
  } else {
    /*@ split_case ptr_eq((*q).front, (*q).back); @*/
    struct int_queueCell *prev = q->back;
    q->back->next = c;
    q->back = c;
    /*@ apply aux_induction((*q).front, prev, c, before, (*prev).first); @*/
    return;
  }
}
