# Imperative queues, verified

To verify the queue operations, we'll need to add some annotations,
as usual.

The basic definitions don't change.  They are explained in the
testing version of this chapter.

```c title="exercises/queue/c_types.h"
--8<--
exercises/queue/c_types.h
--8<--
```

```c title="exercises/queue/cn_types_1.h"
--8<--
exercises/queue/cn_types_1.h
--8<--
```

```c title="exercises/queue/cn_types_2.verif.h"
--8<--
exercises/queue/cn_types_2.verif.h
--8<--
```

```c title="exercises/queue/cn_types_3.verif.h"
--8<--
exercises/queue/cn_types_3.verif.h
--8<--
```

```c title="exercises/queue/allocation.verif.h"
--8<--
exercises/queue/allocation.verif.h
--8<--
```

```c title="exercises/queue/empty.verif.c"
--8<--
exercises/queue/empty.verif.c
--8<--
```

## Push

The push and pop operations are more interesting. Let's look at `push`
first.  Here's the unannotated C code.

```c title="exercises/queue/push_orig.broken.c"
--8<--
exercises/queue/push_orig.broken.c
--8<--
```

One thing you might find odd about this code (and that's a bit
different from the testing version) is that there's a `return`
statement at the end of each branch of the conditional, rather than a
single `return` at the bottom. The reason for this is that, when CN
analyzes a function body containing a conditional, it effectively
_copies_ all the code after the conditional into each of the
branches. After that happens, if verification encounters an error
related to this code -- e.g., "you didn't establish the `ensures`
conditions at the point of returning -- the error message will be
confusing because it will not be clear which branch of the conditional
it is associated with.

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

{{ todo("BCP: Not sure I can explain what 'pointer' means here, or why we don't need to declare more specific types for these arguments to the lemma. ") }}
{{ todo("Dhruv: See above comments about strong updates: in a requires/ensures, the types are given by the arguments in scope, but here we don't have that.") }}

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
just the cells from `front` to `p` and then `Snoc` on the single
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

## Pop

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

{{ later("BCP: the word 'unpack' is mysterious here. ") }}

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
annotation is needed because the `Snoc` function is recursive, so CN
doesn't do the unfolding automatically.

Finally, when the queue contains two or more elements, we need to
deallocate the front cell, return its `first` field, and redirect
the `front` field of the queue structure to point to the next cell.
To push the verification through, we need a simple lemma about the
`Snoc` function:

```c title="exercises/queue/pop_lemma.h"
--8<--
exercises/queue/pop_lemma.h
--8<--
```

The crucial part of this lemma is the last three lines, which express
a simple, general fact about `Snoc`:
if we form a sequence by calling `Snoc` to add a final element
`B.first` to a sequence with head element `x` and tail `Q`, then the
head of the resulting sequence is still `x`, and its tail is `Snoc
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

{{ todo("BCP: The thing about ghost values is mysterious.  How to say it better?") }}

(The only reason we can't currently prove this lemma in CN is that we
don't have `take`s in CN statements.  This is just a simple
unfolding.)  {{ todo("BCP: Ugh. ") }}

## Exercises

_Exercise_:
Investigate what happens when you make each of the following changes
to the queue definitions. What error does CN report? Where are the
telltale clues in the error report that suggest what the problem was?

- Remove `assert (is_null(B.next));` from `QueueFB`.
- Remove `assert (is_null(B.next));` from `QueueAux`.
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
{{ later("BCP: Again, this has not been shown to be
possible, but Dhruv believes it should be!  ") }}
