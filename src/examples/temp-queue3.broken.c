/* queue.c */

#include "list.h"
#include "list_snoc_spec.h"

/*@
lemma snoc_nil (i32 foo)
  requires true;
  ensures snoc (Seq_Nil{}, foo) == Seq_Cons {head: foo, tail: Seq_Nil{}};
@*/

struct int_queue {
  struct int_queueCell* head;
  struct int_queueCell* tail;
};

struct int_queueCell {
  int first;
  struct int_queueCell* next;
};

/*@
predicate (datatype seq) IntQueue (pointer q) {
  take H = Owned<struct int_queue>(q);
  take Q = IntQueue1(q,H);
  return Q;
}

predicate (datatype seq) IntQueue1 (pointer dummy, struct int_queue H) {
  if (is_null(H.head) || is_null(H.tail)) {
    assert (is_null(H.head) && is_null(H.tail));
    return (Seq_Nil{});
  } else {
    assert (!is_null(H.head) && !is_null(H.tail));
    take T = Owned<struct int_queueCell>(H.tail);
    assert (is_null(T.next));
    take Q = IntQueueAux (H.head, H.tail, T.first);
    return Q;
  }
}

predicate (datatype seq) IntQueueAux (pointer h, pointer t, i32 lastVal) {
  if (h == t) {
    return (Seq_Cons{head: lastVal, tail: Seq_Nil{}});
  } else {
    take C = Owned<struct int_queueCell>(h);
    take TL = IntQueueAux(C.next, t, lastVal);
    return (Seq_Cons { head: C.first, tail: TL });
  }
}

@*/

// ---------------------------------------------------------------------

extern struct int_queue *mallocIntQueue();
/*@ spec mallocIntQueue();
    requires true;
    ensures take u = Block<struct int_queue>(return);
            return != NULL;
@*/ // 'return != NULL' should not be needed

extern void freeIntQueue (struct int_queue *p);
/*@ spec freeIntQueue(pointer p);
    requires take u = Block<struct int_queue>(p);
    ensures true;
@*/

extern struct int_queueCell *mallocIntQueueCell();
/*@ spec mallocIntQueueCell();
    requires true;
    ensures take u = Block<struct int_queueCell>(return);
            return != NULL;
@*/ // 'return != NULL' should not be needed

extern void freeIntQueueCell (struct int_queueCell *p);
/*@ spec freeIntQueueCell(pointer p);
    requires take u = Block<struct int_queueCell>(p);
    ensures true;
@*/

// -----------------------------------------------------------------

struct int_queue* IntQueue_empty ()
/*@ ensures take ret = IntQueue(return);
            ret == Seq_Nil{};
@*/
{
  struct int_queue *p = mallocIntQueue();
  p->head = 0;
  p->tail = 0;
  return p;
}

int IntQueue_pop (struct int_queue *q)
/*@ requires take before = IntQueue(q);
             before != Seq_Nil{};
    ensures take after = IntQueue(q);
            after == tl(before);
            return == hd(before);
@*/
{
  /*@ split_case (*q).head == NULL; @*/
  /*@ split_case (*q).tail == NULL; @*/
  // This is needed to unfold IntQueueAux, I guess?
  /*@ split_case (*q).head == (*q).tail; @*/
  struct int_queueCell* h = q->head;
  /*@ split_case (*h).next == NULL; @*/
  int x = h->first;
  if (h->next == 0) {
    // This line was missing originally -- good pedagogy to fix in stages??
    freeIntQueueCell(h);
    q->head = 0;
    q->tail = 0;
    return x;
  } else {
    // Needs to deallocate here too!
    q->head = h->next;
    return x;
  }
  // The return was originally here -- make sure to comment on why it got moved!
}

// Notes:
// - When I tried /*@ unfold IntQueueAux (H.head, H.tail, T.first); @*/
//   I was confused by "the specification function `IntQueueAux' is not declared".
//   I guess this is, again, the distinction between functions and predicates...?
// - Seq_Cons is awkward for several reasons:
//     - long / verbose (nothing to do about that, I guess)
//     - Seq is capitalized, but it means seq
//     - most important part is buried in the middle
//     - What are the established C conventions here??
// - lastVal can be eliminated, I think
