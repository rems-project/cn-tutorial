# Imperative Queues

{{ todo("BCP: Zain points out that the lemma in `push_lemma.h` might
be wrong when `P.next` is `NULL`...  To fix it, try taking ownership[
of `p.next in both the pre- and the postcondition of the push lemma.")}}

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
type from the list examples earlier in the tutorial as the result type
when we `take` a queue from the heap.

```c title="exercises/queue/cn_types_1.test.h"
--8<--
exercises/queue/cn_types_1.test.h
--8<--
```

Given a pointer to a `queue` struct, this predicate grabs ownership
of the structthen hands off to an
auxiliary predicate `QueueFB`. Note that `QueuePtr_At` returns a
`List` -- that is, the abstract view of a queue heap structure is
simply the sequence of elements that it contains. The difference
between a queue and a singly or doubly linked list is simply one of
concrete representation.

{{ todo("BCP: Explain why the asserts are needed.  (Testing fails if
we remove them.)") }}

`QueueFB` is where the interesting part starts. Conceptually,
it is part of `QueuePtr_At`, but CN currently allows
conditional expressions only at the beginning of predicate
definitions, not after a `take`, so we need to make a separate
auxiliary predicate.

```c title="exercises/queue/cn_types_2.test.h"
--8<--
exercises/queue/cn_types_2.test.h
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
`Snoc` on the very last element.

{{ todo("BCP: The asserts here are not needed, but the ones above and
below are.  Do we keep them and explain them?  What is the
explanation??") }}

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

Otherwise, we `take` the fields of the `f`, make a recursive
call to `QueueAux` to process the rest of the cells, and cons the
`first` field of this cell onto the resulting sequence before
returning it. Again, we need to help the CN verifier by explicitly
informing it of the invariant that we know, that `F.next` cannot be
null if `f` and `b` are different.

{{ todo("BCP: The asserts here seem to be sort-of-needed: removing
them leads to a ton of discards.  Why?  How do we explain this?") }}

To make all this work, we also need a bit of boilerplate: just as with
linked lists, we need to be able to allocate and deallocate queues and
queue cells. There are no interesting novelties here.

```c title="exercises/queue/allocation.test.h"
--8<--
exercises/queue/allocation.test.h
--8<--
```

<!-- ====================================================================== -->

## Exercises

_Exercise_: The function for creating an empty queue just needs to set
both of its fields to NULL. See if you can fill in its specification.

```c title="exercises/queue/empty.test.c"
--8<--
exercises/queue/empty.test.c
--8<--
```

<!-- ====================================================================== -->

_Exercise_: The push and pop operations are more involved. Let's look
at `push` first.  Here's the unannotated C code.

```c title="exercises/queue/push.test.c"
--8<--
exercises/queue/push.test.c
--8<--
```

Write down a reasonable top-level specification for this function and
test that the code satisfies it.
{{ later("What about mutation testing?") }}

<!-- ====================================================================== -->

_Exercise_: Now let's look at the `pop` operation. Here is the un-annotated
version:

```c title="exercises/queue/pop_orig.broken.c"
--8<--
exercises/queue/pop_orig.broken.c
--8<--
```

Write down a top-level specification and test that the code satisfies it.

{{ later("BCP: Needs some more exercises?") }}
