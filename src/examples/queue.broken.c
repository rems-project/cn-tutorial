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
predicate (datatype seq) IntQueue(pointer q) {
  take H = Owned<struct int_queue>(q);
  take Q = IntQueue1(q,H);
  return Q;
}

predicate (datatype seq) IntQueue1(pointer dummy, struct int_queue H) {
  if (is_null(H.head)) {
    assert (is_null(H.tail));
    return (Seq_Nil{});
  } else {
    assert (!is_null(H.tail));
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

/*@
function [rec] (datatype seq) push (datatype seq xs, i32 y) {
  snoc (xs, y)
}

function [rec] (i32) pop (datatype seq xs, i32 y) {
  hd (xs)
}
@*/

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
  int x = q->head->first;
  if (q->head->next == 0) {
    q->head = 0;
    q->tail = 0;
  } else {
    q->head = q->head->next;
  }
  return x;
}

void IntQueue_push (int x, struct int_queue *q)
/*@ requires take before = IntQueue(q);
    ensures take after = IntQueue(q);
            after == snoc (before, x);
@*/
{
  struct int_queueCell *c = mallocIntQueueCell();
  c->first = x;
  c->next = 0;
  if (q->tail == 0) {
    /*@ split_case (*q).head == NULL; @*/
    /*@ apply snoc_nil(x); @*/
    // And then this??
    /*@ split_case (*q).tail == NULL; @*/
    q->head = c;
    q->tail = c;
  } else {
    // This is needed next:
    /*@ split_case (*q).head == NULL; @*/
    // And then this??
    /*@ split_case (*q).tail == NULL; @*/
    q->tail->next = c;
    q->tail = c;
  }
}
