#include "list1.h"
#include "list2.h"
#include "list3.h"
#include "list_snoc_spec.h"

/*@
lemma snoc_nil (i32 z)
  requires true;
  ensures snoc (Seq_Nil{}, z) == Seq_Cons {head: z, tail: Seq_Nil{}};
@*/

/*@
lemma snoc_nonempty (pointer h, pointer t, i32 z)
  requires take l = IntQueueAux(h, t);
  ensures take l2 = IntQueueAux(h, t);
          l == l2;
          snoc(l, z) != Seq_Nil{};
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
  assert (is_null(H.head) && is_null(H.tail) || !is_null(H.head) && !is_null(H.tail));
  take Q = IntQueue1(H.head, H.tail);
  return Q;
}

predicate (datatype seq) IntQueue1 (pointer head, pointer tail) {
  if (is_null(head)) {
    return Seq_Nil{};
  } else {
    take T = Owned<struct int_queueCell>(tail);
    assert (is_null(T.next));
    take Q = IntQueueAux (head, tail);
    return snoc(Q, T.first);
  }
}

predicate (datatype seq) IntQueueAux (pointer h, pointer t) {
  if (h == t) {
    return Seq_Nil{};
  } else {
    take C = Owned<struct int_queueCell>(h);
    assert (!is_null(C.next));  // HERE IS THE KEY!
    take TL = IntQueueAux(C.next, t);
    return Seq_Cons { head: C.first, tail: TL };
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

extern struct int_queueCell *mallocIntQueueCell(struct int_queueCell*);
/*@ spec mallocIntQueueCell(pointer p);
    requires true;
    ensures take u = Block<struct int_queueCell>(return);
            return != p;
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

/*@ lemma snoc_cong(pointer h, pointer t, datatype seq r, i32 x)
  requires
    take l = IntQueueAux(h, t);
    l == snoc (r, x);
  ensures
    take l2 = IntQueueAux(h, t);
    l == l2;
    l == snoc(r, x);
@*/

void IntQueue_push (int x, struct int_queue *q)
/*@ requires take before = IntQueue(q);
    ensures take after = IntQueue(q);
            after == snoc (before, x);
@*/
{
  struct int_queueCell *c = mallocIntQueueCell(q->head);
  c->first = x;
  c->next = 0;
  if (q->tail == 0) {
    /*@ assert (before == Seq_Nil{}); @*/
    q->head = c;
    q->tail = c;
    return;
  } else {
    /*@ split_case (*q).head == (*q).tail; @*/
    /*@ apply snoc_nonempty((*q).head, (*q).tail, (*(*q).tail).first); @*/
    /*@ assert (before != Seq_Nil{}); @*/
    q->tail->next = c;
    q->tail = c;
    /*@ unfold snoc(before, x); @*/
    return;
  }
}

// Notes:
// - When I tried /*@ unfold IntQueueAux (H.head, H.tail, T.first); @*/
//   I was confused by "the specification function `IntQueueAux' is not
//   declared".
//   I guess this is, again, the distinction between functions and
//   predicates...?
// - Seq_Cons is awkward for several reasons:
//     - long / verbose (nothing to do about that, I guess)
//     - Seq is capitalized, but it means seq
//     - most important part is buried in the middle
//     - What are the established C conventions here??
// - lastVal can be eliminated, I think  (maybe?!)
// - The fact that some of the Constraints in the error report are forced while
//   others are random values filled in by the SMT solver is pretty problematic
// - There might be a better whole way to do this, using "list segments"
//   a la Chargueraud
