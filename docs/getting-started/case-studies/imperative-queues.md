# Imperative Queues

A queue is a linked list with constant-time operations for adding
things to one end (the "back") and removing them from the other (the
"front"). Here are the C type definitions:

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
it is part of `QueuePTR`, but CN currently allows
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
one cell in the list), and we need to be careful not to `take` this
cell twice.

Accordingly, we begin by `take`-ing the tail cell and passing it
separately to the `QueueAux` predicate, which has the job of
walking down the cells from the front and gathering all the rest of
them into a sequence. We take the result from `QueueAux` and
`snoc` on the very last element.

<span style="color:red">BCP: Explain the asserts.  (Why) are they useful
for testing?  If they are not useful, make a testing-only version
that omits them!  Ditto the QueueAux predicate below.</span>

Finally, the `QueueAux` predicate recurses down the list of
cells and returns a list of their contents.

```c title="exercises/queue/cn_types_3.test.h"
--8<--
exercises/queue/cn_types_3.test.h
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

```c title="exercises/queue/allocation.test.h"
--8<--
exercises/queue/allocation.test.h
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

```c title="exercises/queue/push.test.c"
--8<--
exercises/queue/push.test.c
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

```c title="solutions/queue/push.test.c"
--8<--
solutions/queue/push.test.c
--8<--
```

<!-- ====================================================================== -->

Now let's look at the `pop` operation. Here is the un-annotated
version:

```c title="exercises/queue/pop_orig.broken.c"
--8<--
exercises/queue/pop_orig.broken.c
--8<--
```

_Exercise_: Again, before reading on, see if you can write down a
plausible top-level specification and test its correctness.

Here is the annotated `pop` code:

```c title="exercises/queue/pop.c"
--8<--
exercises/queue/pop.c
--8<--
```

<span style="color:red">BCP: Needs some more exercises?</span>
