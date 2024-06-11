/* queue.c */

#include "list1.h"
#include "list2.h"
#include "list3.h"
#include "list_snoc_spec.h"

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
  // CN bug: parser associativity needs fixing!
  assert ((is_null(H.head) && is_null(H.tail)) || (!is_null(H.head) && !is_null(H.tail)));
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
/*@
lemma tl_snoc(pointer head, pointer tail, datatype seq before, i32 popped)
requires
    take T = Owned<struct int_queueCell>(tail);
    is_null(T.next);
    take Q = IntQueueAux(head, tail);
    let after = snoc(Q, T.first);
    before == snoc (Seq_Cons{head: popped, tail: Q}, T.first);
ensures
    take T2 = Owned<struct int_queueCell>(tail);
    T == T2;
    is_null(T.next);
    take Q2 = IntQueueAux(head, tail);
    Q == Q2;
    after == tl(before);
    popped == hd(before);
@*/

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
  /*@ split_case is_null(h); @*/
  // This originally tested for h->next == 0, but this didn't seem to fit the structure of
  // the verification; this way works better, at least for the first branch.  But would
  // it have been possible to verify it the other way?
  if (h == t) {
    int x = h->first;
    // This line was missing originally -- good pedagogy to fix in stages??
    freeIntQueueCell(h);
    q->head = 0;
    q->tail = 0;
    /*@ unfold snoc(Seq_Nil{}, x); @*/
    return x;
  } else {
    int x = h->first;
    struct int_queueCell* n = h->next;
    q->head = n;
    // Needs to deallocate here too!
    freeIntQueueCell(h);
    /*@ apply tl_snoc(n, (*q).tail, before, x); @*/
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


/*@
// A bit heavy handed but couldn't figure out a better way to state this

lemma snoc_snoc(pointer head, pointer tail, datatype seq before, i32 pushed)
requires
    take T = Owned<struct int_queueCell>(tail);
    is_null(T.next);
    T.first == pushed;
    take Q = IntQueueAux(head, tail);
    let after = snoc(Q, T.first);
ensures
    take T2 = Owned<struct int_queueCell>(tail);
    T == T2;
    take Q2 = IntQueueAux(head, tail);
    Q == Q2;
    before == Q;

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
    struct int_queueCell *prev = q->tail;
    q->tail->next = c;
    q->tail = c;
    /*@ split_case (*(*q).head).next == c; @*/
    /*@ apply snoc_snoc((*q).head, c, before, x); @*/
    // Need to convince CN that prev is not dangling...
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
