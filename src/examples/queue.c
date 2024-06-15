#include "list_c_types.h"
#include "list_cn_types.h"
#include "list_hdtl.h"
#include "list_snoc.h"

#include "queue_c_types.h"

/*@
predicate (datatype seq) IntQueuePtr (pointer q) {
  take H = Owned<struct int_queue>(q);
  assert (   (is_null(H.front)  && is_null(H.back)) 
          || (!is_null(H.front) && !is_null(H.back)));
  take Q = IntQueueFB(H.front, H.back);
  return Q;
}

predicate (datatype seq) IntQueueFB (pointer front, pointer back) {
  if (is_null(front)) {
    return Seq_Nil{};
  } else {
    take T = Owned<struct int_queueCell>(back);
    assert (is_null(T.next));
    take Q = IntQueueAux (front, back);
    return snoc(Q, T.first);
  }
}

predicate (datatype seq) IntQueueAux (pointer h, pointer t) {
  if (ptr_eq(h,t)) {
    return Seq_Nil{};
  } else {
    take C = Owned<struct int_queueCell>(h);
    assert (!is_null(C.next));  
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
            !ptr_eq(return,NULL);
@*/ 

extern void freeIntQueue (struct int_queue *p);
/*@ spec freeIntQueue(pointer p);
    requires take u = Block<struct int_queue>(p);
    ensures true;
@*/

extern struct int_queueCell *mallocIntQueueCell();
/*@ spec mallocIntQueueCell();
    requires true;
    ensures take u = Block<struct int_queueCell>(return);
            !is_null(return);
@*/ 

extern void freeIntQueueCell (struct int_queueCell *p);
/*@ spec freeIntQueueCell(pointer p);
    requires take u = Block<struct int_queueCell>(p);
    ensures true;
@*/

// -----------------------------------------------------------------

struct int_queue* IntQueue_empty ()
/*@ ensures take ret = IntQueuePtr(return);
            ret == Seq_Nil{};
@*/
{
  struct int_queue *p = mallocIntQueue();
  p->front = 0;
  p->back = 0;
  return p;
}

/*@
lemma tl_snoc(pointer front, pointer back, datatype seq before, i32 popped)
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
  // The return was originally here -- make sure to comment on why it got moved!
}

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

// Notes:
// - There might be a better whole way to do this whole example, using "list segments"
//   a la Chargueraud
