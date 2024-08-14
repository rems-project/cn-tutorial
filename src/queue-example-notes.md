2# Notes

- Bad definition of snoc (same as rev). How to spot? Look at constraint context, specifically snoc(listQ, x) == match listQ {Seq\_Nil {} => {Seq\_Nil {}}Seq\_Cons {Head: h, Tail: zs} => {snoc(rev(zs), h)}}. Other big clue: applying lemma snoc_nil results in an inconsistent context. This is really nasty because snoc(Nil{}, x) ends up reducing to itself.

- Code used q->tail == 0 but predicate was testing q->Head. Can adjust predicate, code, or use a split_case.

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

    predicate (datatype List) IntQueue(pointer q) {
      take H = Owned<struct int_queue>(q);
      take Q = IntQueue1(q,H);
      return Q;
    }

    predicate (datatype List) IntQueue1(pointer dummy, struct int_queue H) {
      if (is_null(H.Head)) {
        assert (is_null(H.tail));
        return (Nil{});
      } else {
        assert (!is_null(H.tail));
        take Q = IntQueueAux (H.Head, H.tail);
        return Q;
      }
    }

    predicate (datatype List) IntQueueAux(pointer h, pointer t) {
      take C = Owned<struct int_queueCell>(h);
      take L = IntQueueAux1(h, C, t);
      return L;
    }

    predicate (datatype List) IntQueueAux1
                               (pointer h, struct int_queueCell C, pointer t) {
      if (is_null(C.next)) {
        assert (h == t);
        return (Cons{Head: C.first, Tail: Nil{}});
      } else {
        take TL = IntQueueAux(C.next, t);
        return (Cons { Head: C.first, Tail: TL });
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

    Cons {Head: x, Tail: Nil {}} == snoc(l, x)

while the list of Terms shows that

    Cons {Head: x, Tail: Nil {}} == snoc(l, x)

has value false!

I.e., something is very wrong.

First, we have to find the path to the error.  Either decode the HTML
or put in some returns in the branches of the if.  This tells us that
the problem is in the first branch.

We see

    temp-queue1b.broken.c:95:5: error: Unprovable constraint
        return;
        ^~~~~~~
    Constraint from temp-queue1b.broken.c:86:13:
                ret == snoc (l, x);
                ^~~~~~~~~~~~~~~~~~~

To make progress, we need to unfold snoc.  How do we know this?
Because the constraint that is problematic involves a snoc, and snoc
is recursive, so we should expect to have to unfold at some point.
(Non-recursive things are always inlined, but recursive ones obviously
not, so even to look "one level deep" we need an unfold.)

Once we've unfolded, we get some more hints:

  - Look at the value of l in Terms: Cons {Head: 0i32, Tail: Nil {}}
  - But we are in the empty queue case, so this seems fishy.
  - Now, in the constraints, we see   l == unpack_IntQueue1.Q
  - Then look at the resources and see that unpack_IntQueue1.Q has not
    been unpacked in the final line:
        IntQueue1(q, unpack_IntQueue1.H)(unpack_IntQueue1.Q)
  - This means that CN did not have enough information to decide which
    way the conditional at the beginning of IntQueue1 is going to go.
  - But the condition is testing H.Head, while the conditional in the
    code is testing the tail field!
  - We could get around this mismatch by adjusting the condition
    itself, or by adjusting the predicate.  E.g., we could change the
    predicate to test *both* for null at the beginning, so that it
    doesn't matter which one you test.

This tells us to look at snoc, which turns out to be very wrong!

    function [rec] (datatype List) snoc(datatype List xs, i32 y) {
      match xs {
        Nil {} => {
          Nil {}
        }
        Cons {Head : h, Tail : zs}  => {
          snoc (rev(zs), h)
        }
      }
    }


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
        /*@ split_case q->head == NULL; @*/
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

    predicate (datatype List) IntQueue(pointer q) {
      take H = Owned<struct int_queue>(q);
      take Q = IntQueue1(q,H);
      return Q;
    }

    predicate (datatype List) IntQueue1(pointer dummy, struct int_queue H) {
      if (is_null(H.Head)) {
        assert (is_null(H.tail));
        return (Nil{});
      } else {
        assert (!is_null(H.tail));
        take T = Owned<struct int_queueCell>(H.tail);
        assert (is_null(T.next));
        take Q = IntQueueAux (H.Head, H.tail, T.first);
        return Q;
      }
    }

    predicate (datatype List) IntQueueAux (pointer h, pointer t, i32 lastVal) {
      if (h == t) {
        return (Cons{Head: lastVal, Tail: Nil{}});
      } else {
        take C = Owned<struct int_queueCell>(h);
        take TL = IntQueueAux(C.next, t, lastVal);
        return (Cons { Head: C.first, Tail: TL });
      }
    }

This matches the access pattern of the push implementation, and
it... works??
