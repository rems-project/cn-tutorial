#include "queue_headers.h"

/*@
type_synonym result = { datatype seq after, datatype seq before }

predicate (result) Queue_pop_lemma(pointer front, pointer back, i32 popped) {
  if (is_null(front)) {
    return { after: Seq_Nil{}, before: snoc(Seq_Nil{}, popped) };
  } else {
    take B = Owned<struct int_queueCell>(back);
    assert (is_null(B.next));
    take L = IntQueueAux (front, back);
    return { after: snoc(L, B.first), before: snoc(Seq_Cons {head: popped, tail: L}, B.first) };
  }
}
@*/

void snoc_fact(struct int_queueCell *front, struct int_queueCell *back, int x)
/*@
requires
    take Q = IntQueueAux(front, back);
    take B = Owned<struct int_queueCell>(back);
ensures
    take NewQ = IntQueueAux(front, back);
    take NewB = Owned<struct int_queueCell>(back);
    Q == NewQ; B == NewB;
    let L = snoc (Seq_Cons{head: x, tail: Q}, B.first);
    hd(L) == x;
    tl(L) == snoc (Q, B.first);
@*/
{
    /*@ unfold snoc (Seq_Cons{head: x, tail: Q}, B.first); @*/
}

void snoc_fact_unified(struct int_queueCell *front, struct int_queueCell *back, int x)
/*@
requires
      take AB = Queue_pop_lemma(front, back, x);
ensures
      take NewAB = Queue_pop_lemma(front, back, x);
      AB == NewAB;
      AB.after == tl(AB.before);
      x == hd(AB.before);
@*/
{
    if (!front) {
        /*@ unfold snoc(Seq_Nil{}, x); @*/
    } else {
        snoc_fact(front, back, x);
    }
}

int IntQueue_pop (struct int_queue *q)
/*@ requires take before = IntQueuePtr(q);
             before != Seq_Nil{};
    ensures take after = IntQueuePtr(q);
            after == tl(before);
            return == hd(before);
@*/
{
  /*@ split_case is_null((*q).front); @*/
  struct int_queueCell* h = q->front;
  /*@ split_case ptr_eq(h,(*q).back); @*/
  int x = h->first;
  q->front = h->next;
  freeIntQueueCell(h);
  if (!q->front) q->back = 0;
  snoc_fact_unified(q->front, q->back, x);
  return x;
}

