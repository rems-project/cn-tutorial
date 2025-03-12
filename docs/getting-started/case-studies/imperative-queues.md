# Imperative Queues

A queue is a linked list with O(1) operations for adding things to one
end (the "back") and removing them from the other (the "front"). Here
are the C type definitions:

```c title="exercises/queue/c_types.h"
--8<--
exercises/queue/c_types.h
--8<--
```

A queue consists of a pair of pointers, one pointing to the front
element, which is the first in a linked list of `queue_cell`s,
the other pointing directly to the last cell in this list. If the
queue is empty, both pointers are NULL.

Abstractly, a queue just represents a list, so we can reuse the `List`
type from the list examples earlier in the tutorial.

```c title="exercises/queue/cn_types_1.h"
--8<--
exercises/queue/cn_types_1.h
--8<--
```

Given a pointer to a `queue` struct, this predicate grabs ownership
of the struct, asserts that the `front` and `back` pointers must
either both be NULL or both be non-NULL, and then hands off to an
auxiliary predicate `QueueFB`. Note that `QueuePtr_At` returns a
`List` -- that is, the abstract view of a queue heap structure is
simply the sequence of elements that it contains. The difference
between a queue and a singly or doubly linked list is simply one of
concrete representation.

`QueueFB` is where the interesting part starts. (Conceptually,
`QueueFB` is part of `QueuePTR`, but CN currently allows
conditional expressions only at the beginning of predicate
definitions, not after a `take`, so we need to make a separate
auxiliary predicate.)

```c title="exercises/queue/cn_types_2.h"
--8<--
exercises/queue/cn_types_2.h
--8<--
```

First, we case on whether the `front` of the queue is NULL. If so,
then the queue is empty and we return the empty sequence.

If the queue is not empty, we need to walk down the linked list of
elements and gather up all their values into a sequence. But we must
treat the last element of the queue specially, for two reasons.
First, since the `push` operation is going to follow the `back`
pointer directly to the last list cell without traversing all the
others, we need to `take` that element now rather than waiting to
get to it at the end of the recursion starting from the `front`.
Second, and relatedly, there will be two pointers to this final list
cell -- one from the `back` field and one from the `next` field of
the second to last cell (or the `front` pointer, if there is only
one cell in the list), so we need to be careful not to `take` this
cell twice.

Accordingly, we begin by `take`-ing the tail cell and passing it
separately to the `QueueAux` predicate, which has the job of
walking down the cells from the front and gathering all the rest of
them into a sequence. We take the result from `QueueAux` and
`snoc` on the very last element.

The `assert (is_null(B.next))` here gives the CN verifier a crucial
piece of information about an invariant of the representation: The
`back` pointer always points to the very last cell in the list, so
its `next` field will always be NULL.

<!-- TODO: BCP: How to help people guess that this is needed?? -->

Finally, the `QueueAux` predicate recurses down the list of
cells and returns a list of their contents.

```c title="exercises/queue/cn_types_3.h"
--8<--
exercises/queue/cn_types_3.h
--8<--
```

Its first argument (`f`) starts out at `front` and progresses
through the queue on recursive calls; its `b` argument is always a
pointer to the very last cell.

When `f` and `b` are equal, we have reached the last cell and
there is nothing to do. We don't even have to build a singleton
list: that's going to happen one level up, in `QueueFB`.

Otherwise, we `take` the fields of the `f`, make a recurive
call to `QueueAux` to process the rest of the cells, and cons the
`first` field of this cell onto the resulting sequence before
returning it. Again, we need to help the CN verifier by explicitly
informing it of the invariant that we know, that `C.next` cannot be
null if `f` and `b` are different.

Now we need a bit of boilerplate: just as with linked lists, we need
to be able to allocate and deallocate queues and queue cells. There
are no interesting novelties here.

```c title="exercises/queue/allocation.verif.h"
--8<--
exercises/queue/allocation.verif.h
--8<--
```

<!-- ====================================================================== -->

_Exercise_: The function for creating an empty queue just needs to set
both of its fields to NULL. See if you can fill in its specification.

```c title="exercises/queue/empty.c"
--8<--
exercises/queue/empty.c
--8<--
```

<!-- ====================================================================== -->

The push and pop operations are more involved. Let's look at `push`
first.

Here's the unannotated C code -- make sure you understand it.

```c title="exercises/queue/push_orig.broken.c"
--8<--
exercises/queue/push_orig.broken.c
--8<--
```

_Exercise_: Before reading on, see if you can write down a reasonable
top-level specification for this operation.

One thing you might find odd about this code is that there's a
`return` statement at the end of each branch of the conditional,
rather than a single `return` at the bottom. The reason for this is
that, when CN analyzes a function body containing a conditional, it
effectively _copies_ all the code after the conditional into each of
the branches. Then, if verification encounters an error related to
this code -- e.g., "you didn't establish the `ensures` conditions at
the point of returning -- the error message will be confusing because
it will not be clear which branch of the conditional it is associated
with.

Now, here is the annotated version of the `push` operation.

```c title="exercises/queue/push.c"
--8<--
exercises/queue/push.c
--8<--
```

The case where the queue starts out empty (`q->back == 0`) is easy.
CN can work it out all by itself.

The case where the starting queue is nonempty is more interesting.
The `push` operation messes with the end of the sequence of queue
elements, so we should expect that validating `push` is going to
require some reasoning about this sequence. Here, in fact, is the
lemma we need.

<!-- TODO: BCP: Not sure I can explain what "pointer" means here, or why we don't need to declare more specific types for these arguments to the lemma. -->
<!-- Dhruv: See above comments about strong updates: in a requires/ensures, the types are given by the arguments in scope, but here we don't have that. -->

```c title="exercises/queue/push_lemma.h"
--8<--
exercises/queue/push_lemma.h
--8<--
```

This says, in effect, that we have two choices for how to read out the
values in some chain of queue cells of length at least 2, starting
with the cell `front` and terminating when we get to the next cell
_following_ some given cell `p` -- call it `c`. We can either
gather up all the cells from `front` to `c`, or we can gather up
just the cells from `front` to `p` and then `snoc` on the single
value from `c`.

When we apply this lemma, `p` will be the old `back` cell and
`c` will be the new one. But to prove it (by induction, of course),
we need to state it more generally, allowing `p` to be any internal
cell in the list starting at `front` and `c` its successor.

The reason we need this lemma is that, to add a new cell at the end of
the queue, we need to reassign ownership of the old `back` cell.
In the precondition of `push`, we took ownership of this cell
separately from the rest; in the postcondition, it needs to be treated
as part of the rest (so that the new `back` cell can now be treated
specially).

One interesting technicality is worth noting: After the assignment
`q->back = c`, we can no longer prove `QueueFB(q->front,
oldback)`, but we don't care about this, since we want to prove
`QueueFB(q->front, q->back)`. However, crucially,
`QueueAux(q->front, oldback)` is still true.

<!-- ====================================================================== -->

Now let's look at the `pop` operation. Here is the un-annotated
version:

```c title="exercises/queue/pop_orig.broken.c"
--8<--
exercises/queue/pop_orig.broken.c
--8<--
```

_Exercise_: Again, before reading on, see if you can write down a
plausible top-level specification. (For extra credit, see how far you
can get with verifying it!)

Here is the fully annotated `pop` code:

```c title="exercises/queue/pop.c"
--8<--
exercises/queue/pop.c
--8<--
```

There are three annotations to explain. Let's consider them in order.

First, the `split_case` on `is_null(q->front)` is needed to tell
CN which of the branches of the `if` at the beginning of the
`QueueFB` predicate it can "unpack". (`QueuePtr_At` can be
unpacked immediately because it is unconditional, but `QueueFB`
cannot.)

<!-- TODO: BCP: the word "unpack" is mysterious here. -->

The guard/condition for `QueueFB` is `is_null(front)`, which is
why we need to do a `split_case` on this value. On one branch of the
`split_case` we have a contradiction: the fact that `before ==
Nil{}` (from `QueueFB`) conflicts with `before != Nil`
from the precondition, so that case is immediate. On the other
branch, CN now knows that the queue is non-empty, as required, and type
checking proceeds.

When `h == q->back`, we are in the case where the queue contains
just a single element, so we just need to NULL out its `front` and
`back` fields and deallocate the dead cell. The `unfold`
annotation is needed because the `snoc` function is recursive, so CN
doesn't do the unfolding automatically.

Finally, when the queue contains two or more elements, we need to
deallocate the front cell, return its `first` field, and redirect
the `front` field of the queue structure to point to the next cell.
To push the verification through, we need a simple lemma about the
`snoc` function:

```c title="exercises/queue/pop_lemma.h"
--8<--
exercises/queue/pop_lemma.h
--8<--
```

The crucial part of this lemma is the last three lines, which express
a simple, general fact about `snoc`:
if we form a sequence by calling `snoc` to add a final element
`B.first` to a sequence with head element `x` and tail `Q`, then the
head of the resulting sequence is still `x`, and its tail is `snoc
(Q, B.first)`.

The `requires` clause and the first three lines of the `ensures`
clause simply set things up so that we can name the various values we
are talking about. Since these values come from structures in the
heap, we need to take ownership of them. And since lemmas in CN are
effectively just trusted functions that can also take in ghost values,
we need to take ownership in both the `requires` and `ensures`
clauses. (Taking them just in the `requires` clause would imply
that they are consumed and deallocated when the lemma is applied --
not what we want!)

<!-- TODO: BCP: The thing about ghost values is mysterious. -->
<!-- How to say it better? -->

(The only reason we can't currently prove this lemma in CN is that we
don't have `take`s in CN statements, because this is just a simple
unfolding.)

<!-- TODO: BCP: Ugh. -->

_Exercise_:
Investigate what happens when you make each of the following changes
to the queue definitions. What error does CN report? Where are the
telltale clues in the error report that suggest what the problem was?

- Remove `assert (is_null(B.next));` from `InqQueueFB`.
- Remove `assert (is_null(B.next));` from `InqQueueAux`.
- Remove one or both of occurrences of `free_queue_cell(f)` in
  `pop_queue`.
- Remove, in turn, each of the CN annotations in the bodies of
  `pop_queue` and `push_queue`.

_Exercise_: The conditional in the `pop` function tests whether or
not `f == b` to find out whether we have reached the last element of
the queue. Another way to get the same information would be to test
whether `f->next == 0`. Can you verify this version?
_Note_: I (BCP) have not worked out the details, so am not sure how hard
this is (or if it is even not possible, though I'd be surprised).
Please let me know if you get it working!

_Exercise_: Looking at the code for the `pop` operation,
it might seem reasonable to move the identical assignments to `x` in both
branches to above the `if`. This doesn't "just work" because the
ownership reasoning is different. In the first case, ownership of
`h` comes from `QueueFB` (because `h == q->back`). In the
second case, it comes from `QueueAux` (because `h !=
q->back`).

Can you generalize the `snoc_facts` lemma to handle both cases? You
can get past the dereference with a `split_case` but formulating the
lemma before the `return` will be a bit more complicated.

<!-- -->

_Note_: Again, this has not been shown to be possible, but Dhruv
believes it should be!


