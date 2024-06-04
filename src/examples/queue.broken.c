/* queue.c */

#include "list.h"
#include "list_rev_spec.h"  /* (For snoc) */

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

// struct int_queue* IntQueue_empty ()
// /*@ ensures take ret = IntQueue(return);
//             ret == Seq_Nil{};
//  @*/
// {
//   return 0;
// }
//
// struct int_queue* IntQueue_cons(int h, struct int_queue* t)
// /*@ requires take l = IntQueue(t);
//     ensures take ret = IntQueue(return);
//             ret == Seq_Cons{ head: h, tail: l};
//  @*/
// {
//   struct int_queue *p = mallocIntQueue();
//   p->head = h;
//   p->tail = t;
//   return p;
// }
