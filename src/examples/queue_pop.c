#include "queue_headers.h"

/*@
lemma tl_snoc (pointer front, pointer back, datatype seq before, i32 popped)
requires
    take T = Owned<struct int_queueCell>(back);
    is_null(T.next);
    take Q = IntQueueAux(front, back);
    let after = snoc(Q, T.first);
    before == snoc (Seq_Cons{head: popped, tail: Q}, T.first);
ensures
    take T2 = Owned<struct int_queueCell>(back);
    T == T2;
    is_null(T.next);
    take Q2 = IntQueueAux(front, back);
    Q == Q2;
    after == tl(before);
    popped == hd(before);
@*/

int IntQueue_pop (struct int_queue *q)
/*@ requires take before = IntQueuePtr(q);
             before != Seq_Nil{};
    ensures take after = IntQueuePtr(q);
            after == tl(before);
            return == hd(before);
@*/
{
  struct int_queueCell* h = q->front;
  struct int_queueCell* t = q->back;
  /*@ split_case is_null(h); @*/
  // This originally tested for h->next == 0, but this didn't seem to fit the structure of
  // the verification; this way works better, at least for the first branch.  But would
  // it have been possible to verify it the other way?
  if (h == t) {
    int x = h->first;
    // This line was missing originally -- good pedagogy to fix in stages??
    freeIntQueueCell(h);
    q->front = 0;
    q->back = 0;
    /*@ unfold snoc(Seq_Nil{}, x); @*/
    return x;
  } else {
    int x = h->first;
    struct int_queueCell* n = h->next;
    q->front = n;
    freeIntQueueCell(h);
    /*@ apply tl_snoc(n, (*q).back, before, x); @*/
    return x;
  }
}

