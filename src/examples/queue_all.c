#ifndef CN_UTILS
void *cn_malloc(unsigned long);
void cn_free_sized(void* p, unsigned long s);
#endif

/* ############################# CN  ############################# */

/*@
datatype seq {
  Seq_Nil {},
  Seq_Cons {i32 head, datatype seq tail}
}

function (i32) hd (datatype seq xs) {
  match xs {
    Seq_Nil {} => {
      0i32
    }
    Seq_Cons {head : h, tail : _} => {
      h
    }
  }
}

function (datatype seq) tl (datatype seq xs) {
  match xs {
    Seq_Nil {} => {
      Seq_Nil {}
    }
    Seq_Cons {head : _, tail : tail} => {
      tail
    }
  }
}

function [rec] (datatype seq) rev(datatype seq xs) {
  match xs {
    Seq_Nil {} => {
      Seq_Nil{}
    }
    Seq_Cons {head: x, tail: zs}  => {
      snoc(rev(zs), x)
    }
  }
}
@*/

/*@
function [rec] (datatype seq) snoc(datatype seq xs, i32 y) {
  match xs {
    Seq_Nil {} => {
      Seq_Cons {head: y, tail: Seq_Nil{}}
    }
    Seq_Cons {head: x, tail: zs}  => {
      Seq_Cons{head: x, tail: snoc (zs, y)}
    }
  }
}
@*/

/* ############################# DEFNS ########################### */

struct int_queue {
  struct int_queueCell* front;
  struct int_queueCell* back;
};

struct int_queueCell {
  int first;
  struct int_queueCell* next;
};

/*@
predicate (datatype seq) IntQueuePtr (pointer q) {
  take Q = Owned<struct int_queue>(q);
  assert (   (is_null(Q.front)  && is_null(Q.back))
          || (!is_null(Q.front) && !is_null(Q.back)));
  take L = IntQueueFB(Q.front, Q.back);
  return L;
}
@*/

/*@
predicate (datatype seq) IntQueueFB (pointer front, pointer back) {
  if (is_null(front)) {
    return Seq_Nil{};
  } else {
    take B = Owned<struct int_queueCell>(back);
    assert (is_null(B.next));
    take L = IntQueueAux (front, back);
    return snoc(L, B.first);
  }
}
@*/

/*@
predicate (datatype seq) IntQueueAux (pointer f, pointer b) {
  if (ptr_eq(f,b)) {
    return Seq_Nil{};
  } else {
    take F = Owned<struct int_queueCell>(f);
    assert (!is_null(F.next));
    take B = IntQueueAux(F.next, b);
    return Seq_Cons{head: F.first, tail: B};
  }
}
@*/

struct int_queue *mallocIntQueue()
/*@ trusted;
    requires true;
    ensures take u = Block<struct int_queue>(return);
            !ptr_eq(return,NULL);
@*/
{
    return cn_malloc(sizeof(struct int_queue));
}

int freeIntQueue (struct int_queue *p)
/*@ trusted;
    requires take u = Block<struct int_queue>(p);
    ensures true;
@*/
{
    cn_free_sized(p, sizeof(struct int_queue));
    return 0;
}

struct int_queueCell *mallocIntQueueCell()
/*@ trusted;
    requires true;
    ensures take u = Block<struct int_queueCell>(return);
            !is_null(return);
@*/
{
    return cn_malloc(sizeof(struct int_queueCell));
}

int freeIntQueueCell (struct int_queueCell *p)
/*@ trusted;
    requires take u = Block<struct int_queueCell>(p);
    ensures true;
@*/
{
    cn_free_sized(p, sizeof(struct int_queueCell));
    return 0;
}

/* ############################# EMP ############################# */

struct int_queue* IntQueue_empty()
/*@ ensures take ret = IntQueuePtr(return);
            ret == Seq_Nil{};
@*/
{
  struct int_queue *p = mallocIntQueue();
  p->front = 0;
  p->back = 0;
  return p;
}

/* ############################# POP ############################# */

// /*@
//
// predicate ({ datatype seq after, datatype seq before }) Queue_pop_lemma(pointer front, pointer back, i32 popped) {
//   if (is_null(front)) {
//     return { after: Seq_Nil{}, before: snoc(Seq_Nil{}, popped) };
//   } else {
//     take B = Owned<struct int_queueCell>(back);
//     assert (is_null(B.next));
//     take L = IntQueueAux (front, back);
//     return { after: snoc(L, B.first), before: snoc(Seq_Cons {head: popped, tail: L}, B.first) };
//   }
// }
// @*/
//
// int snoc_fact(struct int_queueCell *front, struct int_queueCell *back, int x)
// /*@
// requires
//     take Q = IntQueueAux(front, back);
//     take B = Owned<struct int_queueCell>(back);
// ensures
//     take NewQ = IntQueueAux(front, back);
//     take NewB = Owned<struct int_queueCell>(back);
//     Q == NewQ; B == NewB;
//     let L = snoc (Seq_Cons{head: x, tail: Q}, B.first);
//     hd(L) == x;
//     tl(L) == snoc (Q, B.first);
// @*/
// {
//     /*@ unfold snoc (Seq_Cons{head: x, tail: Q}, B.first); @*/
//     return 0;
// }
//
// int snoc_fact_unified(struct int_queueCell *front, struct int_queueCell *back, int x)
// /*@
// requires
//       take AB = Queue_pop_lemma(front, back, x);
// ensures
//       take NewAB = Queue_pop_lemma(front, back, x);
//       AB == NewAB;
//       AB.after == tl(AB.before);
//       x == hd(AB.before);
// @*/
// {
//     if (!front) {
//         /*@ unfold snoc(Seq_Nil{}, x); @*/
//     } else {
//         snoc_fact(front, back, x);
//     }
//     return 0;
// }
//
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
  // snoc_fact_unified(q->front, q->back, x);
  return x;
}

/* ############################ PUSH1 ############################ */

int push_lemma (struct int_queueCell *front, struct int_queueCell *p)
/*@
  trusted;
  requires
      take Q = IntQueueAux(front, p);
      take P = Owned<struct int_queueCell>(p);
  ensures
      take NewQ = IntQueueAux(front, P.next);
      NewQ == snoc(Q, P.first);
@*/
{
}

int IntQueue_push (int x, struct int_queue *q)
/*@ requires take before = IntQueuePtr(q);
    ensures take after = IntQueuePtr(q);
            after == snoc (before, x);
@*/
{
  struct int_queueCell *c = mallocIntQueueCell();
  c->first = x;
  c->next = 0;
  if (q->back == 0) {
    q->front = c;
    q->back = c;
    return 0;
  } else {
    struct int_queueCell *oldback = q->back;
    q->back->next = c;
    q->back = c;
    push_lemma(q->front, oldback);
    // /*@ apply push_lemma ((*q).front, oldback); @*/
    return 0;
  }
}

/* ############################ PUSH2 ############################ */

/*@
lemma assert_not_equal(pointer x, pointer y)
requires
    true;
ensures
    !ptr_eq(x, y);
@*/

int push_induction(struct int_queueCell* front, struct int_queueCell* p)
/*@
  requires
      take Q = IntQueueAux(front, p);
      take P = Owned(p);
      !ptr_eq(front, P.next);
      !is_null(P.next);
  ensures
      take NewQ = IntQueueAux(front, P.next);
      NewQ == snoc(Q, P.first);
@*/
{
    if (front == p) {
        /*@ unfold snoc(Q, P.first); @*/
        return 0;
    } else {
        // Should be derived automatically
        /*@ apply assert_not_equal((*front).next, (*p).next); @*/
        push_induction(front->next, p);
        /*@ unfold snoc(Q, P.first); @*/
        return 0;
    }
}

int IntQueue_push_induction (int x, struct int_queue *q)
/*@ requires take before = IntQueuePtr(q);
    ensures take after = IntQueuePtr(q);
            after == snoc (before, x);
@*/
{
  struct int_queueCell *c = mallocIntQueueCell();
  /*@ apply assert_not_equal((*q).front, c); @*/
  c->first = x;
  c->next = 0;
  if (q->back == 0) {
    q->front = c;
    q->back = c;
    return 0;
  } else {
    struct int_queueCell *oldback = q->back;
    q->back->next = c;
    q->back = c;
    push_induction(q->front, oldback);
    return 0;
  }
}

int assert_23(struct int_queue *q)
/*@ trusted;
    requires take before = IntQueuePtr(q);
    ensures take after = IntQueuePtr(q);
            before == after;
            before == Seq_Cons { head: 3i32, tail: Seq_Cons { head: 2i32, tail: Seq_Nil{} } };
@*/
{
    return 0;
}

int assert_1234(struct int_queue *q)
/*@ trusted;
    requires take before = IntQueuePtr(q);
    ensures take after = IntQueuePtr(q);
            before == after;
            before ==         Seq_Cons { head: 1i32
                      , tail: Seq_Cons { head: 2i32
                      , tail: Seq_Cons { head: 3i32
                      , tail: Seq_Cons { head: 4i32
                      , tail: Seq_Nil{} }}}};
@*/
{
    return 0;
}

/* ############################ MAIN ############################# */
int main()
/*@ trusted; @*/
{

    struct int_queue *queue = IntQueue_empty();
    IntQueue_push(3, queue);
    int x = IntQueue_pop(queue);
    /*@ assert (x == 3i32); @*/

    IntQueue_push_induction(2, queue);
    x = IntQueue_pop(queue);
    /*@ assert (x == 2i32); @*/

    IntQueue_push(3, queue);
    IntQueue_push_induction(2, queue);

    assert_23(queue);

    x = IntQueue_pop(queue);
    /*@ assert (x == 3i32); @*/
    x = IntQueue_pop(queue);
    /*@ assert (x == 2i32); @*/

    IntQueue_push_induction(1, queue);
    IntQueue_push(2, queue);
    IntQueue_push_induction(3, queue);
    IntQueue_push(4, queue);

    assert_1234(queue);

    IntQueue_pop(queue);
    IntQueue_pop(queue);
    x = IntQueue_pop(queue);
    IntQueue_pop(queue);
    /*@ assert (x == 3i32); @*/

    freeIntQueue(queue);

    return 0;
}
