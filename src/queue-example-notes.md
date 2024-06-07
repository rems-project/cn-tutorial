# Notes

- Bad definition of snoc (same as rev). How to spot? Look at constraint context, specifically snoc(listQ, x) == match listQ {Seq\_Nil {} => {Seq\_Nil {}}Seq\_Cons {head: h, tail: zs} => {snoc(rev(zs), h)}}. Other big clue: applying lemma snoc_nil results in an inconsistent context. This is really nasty because snoc(Seq_Nil{}, x) ends up reducing to itself.

- Code used q->tail == 0 but predicate was testing q->head. Can adjust predicate, code, or use a split_case.

- Under-constrained counter-examples are something to be aware of (though the inconsitency came because of the definition of snoc here rather than l here).

d99e65ed01c7a35408b0e409af3f17ece25bc0bf is the tutorial commit (with the correct definition of snoc, but the point at which you originally asked for help)

More notes:
  - path explosion means you can't look at path to error in HTML output
      - it can help to move the return statement (manually explode!)
        to see which path is failing 
      - (should be able to annotate after a conditional to pull things
        back together) 
  - conclude that l is not properly constrained
        because the SMT solver is making crazy choices

# --------------------------------------------------------------------------
# Original version

Here's the predicate for queues:

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

And here's the push operation.

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
        q->head = c;
        q->tail = c;
      } else {
        q->tail->next = c;
        q->tail = c;
      }
    }

This fails because there are not enough annotations in the body of push.

Confusingly, the HTML error report gives this as the unproven constraint

    Seq_Cons {head: x, tail: Seq_Nil {}} == snoc(l, x)

while the list of Terms shows that

    Seq_Cons {head: x, tail: Seq_Nil {}} == snoc(l, x)

has value false!

I.e., something is very wrong.

# --------------------------------------------------------------------------
# Next try

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
        /*@ apply snac_nil(x); @*/
        q->head = c;
        q->tail = c;
      } else {
        q->tail->next = c;
        q->tail = c;
      }
    }

This time the error is:

    temp-queue2.broken.c:86:5: error: Missing resource for writing
        q->tail->next = c;
        ~~~~~~~~~~~~~~^~~
    Resource needed: Block<struct
        int_queueCell*>(member_shift<int_queueCell>(unpack_IntQueue1
        .H
        .tail, next))

This makes more sense.  [But how to articulate the sense that it
makes??] 

# --------------------------------------------------------------------------
# Getting closer

We could fix this by rewriting the push function so that, instead of
following the tail pointer, it recurses down from the head until it
reaches the tail.  This would work (might be a good exercise?), but it
nullifies the whole purpose of having the tail pointer in the first
place.  

Instead, we need to rearrange IntQueue and friends so that we take
ownership of the very last cell in the list at the very beginning, 
instead of at the very end.

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

This matches the access pattern of the push implementation, and
it... works?? 

