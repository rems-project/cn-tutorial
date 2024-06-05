/* queue.c */

#include "list.h"
#include "list_snoc_spec.h"

struct int_queue {
  struct int_queueCell* head;
  struct int_queueCell* tail;
};

struct int_queueCell {
  int first;
  struct int_queueCell* next;
};

// take V = Owned<t>(p) === p |-t-> V

// Why is the argument type just "pointer" with no info about what
// type it points to?

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
    take Q = IntQueueAux (H.head, H.tail);
    return Q;
  }
}

predicate (datatype seq) IntQueueAux(pointer h, pointer t) {
  take C = Owned<struct int_queueCell>(h);
  take L = IntQueueAux1(h, C, t);
  return L;
}

predicate (datatype seq) IntQueueAux1
                           (pointer h, struct int_queueCell C, pointer t) {
  if (is_null(C.next)) {
    assert (h == t);
    return (Seq_Cons{head: C.first, tail: Seq_Nil{}});
  } else {
    take TL = IntQueueAux(C.next, t);
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

/*@
lemma snoc_nil (i32 foo)
  requires true;
  ensures snoc (Seq_Nil{}, foo) == Seq_Cons {head: foo, tail: Seq_Nil{}};
@*/

void IntQueue_push (int x, struct int_queue *q)
/*@ requires take l = IntQueue(q);
    ensures take ret = IntQueue(q);
            ret == snoc (l, x);
@*/
{
  struct int_queueCell *c = mallocIntQueueCell();
  c->first = x;
  c->next = 0;
  if (q->tail == 0) {
    /*@ split_case (*q).head == NULL; @*/
    /*@ apply snoc_nil(x); @*/
    q->head = c;
    q->tail = c;
  } else {
    q->tail->next = c;
    q->tail = c;
  }
}
