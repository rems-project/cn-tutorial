/* queue.c */

#include "list1.h"
#include "list2.h"
#include "list3.h"
#include "list_snoc_spec.h"

/*@
lemma snoc_nil (i32 z)
  requires true;
  ensures snoc (Seq_Nil{}, z) == Seq_Cons {head: z, tail: Seq_Nil{}};
@*/

struct int_queue {
  struct int_queueCell* head;  // Call them front and back!
  struct int_queueCell* tail;
};

struct int_queueCell {
  int first;  // Call it v
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
    assert (!is_null(C.next));  // HERE IS THE KEY!
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
  // This is needed to unfold IntQueueAux, I guess?
  struct int_queueCell* h = q->head;
  struct int_queueCell* t = q->tail;
  /*@ split_case h == NULL; @*/
  /*@ split_case t == NULL; @*/
  /*@ split_case h == t; @*/
  int x = h->first;
  // This originally tested for h->next == 0, but this didn't seem to fit the structure of
  // the verification; this way works better, at least for the first branch.  But would
  // it have been possible to verify it the other way?
  if (h == t) {
    // This line was missing originally -- good pedagogy to fix in stages??
    freeIntQueueCell(h);
    q->head = 0;
    q->tail = 0;
    return x;
  } else {
    struct int_queueCell* n = h->next;
    q->head = n;
    // Needs to deallocate here too!
    freeIntQueueCell(h);
    return x;
  }
  // The return was originally here -- make sure to comment on why it got moved!
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
  struct int_queueCell* t = q->tail;
  struct int_queueCell* h = q->head;
  if (t == 0) {
    /*@ split_case h == NULL; @*/
    q->head = c;
    q->tail = c;
    // Figuring out that this was needed was a useful/interesting bit of detective work
    /*@ apply snoc_nil(x); @*/
    return;
  } else {
    /*@ split_case h == NULL; @*/
    /*@ split_case h == t; @*/
    t->next = c;
    q->tail = c;
    // This appears to be wanted, but not sure why!
    /*@ apply snoc_nil(x); @*/
    return;
  }
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
// - lastVal can be eliminated, I think  (maybe?!)
// - The fact that some of the Constraints in the error report are forced while
//   others are random values filled in by the SMT solver is pretty problematic
// - There might be a better whole way to do this, using "list segments" a la Chargueraud
