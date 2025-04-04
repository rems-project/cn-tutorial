# Doubly-linked Lists

{{ later("BCP: The rest of the tutorial (from here to the end) needs to be checked for consistency of naming and capitalization conventions. ") }}

A doubly linked list is a linked list where each node has a pointer
to both the next node and the previous node. This allows for constant-time
operations for adding or removing nodes anywhere in the list.

Because of all the sharing in this data structure, the separation
reasoning is a bit tricky. We'll give you the core definitions and
then invite you to help fill in the specifications for some of the
functions that manipulate doubly linked lists.

## Types

First, here is the C type definition:

```c title="exercises/dllist/c_types.h"
--8<--
exercises/dllist/c_types.h
--8<--
```

The idea behind the representation of this list is that we don't keep
track of the front or back, but rather we take any node in the list
and have a sequence to the left and to the right of that node. The `left`
and `right` are from the point of view of the node itself, so `left`
is kept in reverse order. Additionally, similarly to in the
Imperative Queues example, we can reuse the `List` type.

```c title="exercises/dllist/cn_types.h"
--8<--
exercises/dllist/cn_types.h
--8<--
```

The predicate for this datatype is a bit complicated. The idea is that
we first own the node that is passed in. Then we follow all of the
`prev` pointers to own everything backwards from the node, and finally
all the `next` pointers to own everything forwards from the node, to
construct the `left` and `right` fields.

```c title="exercises/dllist/predicates.h"
--8<--
exercises/dllist/predicates.h
--8<--
```

Note that `DlList_at` takes ownership of the node passed in, and then
calls `Take_Left` and `Take_Right`, which recursively take
ownership of the rest of the list.

{{ todo("BCP: Has ptr_eq been explained?  It's useful
-- should be! ") }}

Also, notice that `Take_Right` and `Take_Left` include `ptr_eq`
assertions for the `prev` and `next` pointers. This is to ensure that
the nodes in the list are correctly doubly linked. For example, the
line `assert (ptr_eq(n.prev, prev_pointer));` in `Take_Right`
ensures that the current node correctly points backward to the
previous node in the list. The line `assert(ptr_eq(prev_node.next,
p));` ensures that the previous node correctly points forward to the
current node.

{{ todo("BCP: Are these asserts needed for testing?  Try it and see!") }}

Before we move on to the functions that manipulate doubly linked
lists, we need to define a few "getter" functions that will allow us
to access the fields of our `DlList` datatype. This will make the
specifications easier to write.

```c title="exercises/dllist/getters.h"
--8<--
exercises/dllist/getters.h
--8<--
```

We also need the usual boilerplate for allocation and deallocation.

```c title="exercises/dllist/allocation.test.h"
--8<--
exercises/dllist/allocation.test.h
--8<--
```

For convenience, we gather all of these files into a single header file.

```c title="exercises/dllist/headers.test.h"
--8<--
exercises/dllist/headers.test.h
--8<--
```

<!-- ====================================================================== -->

## Singleton

Now we can move on to an initialization function. Since an empty list
is represented as a null pointer, we will look at initializing a
singleton list (or in other words, a list with only one item).

```c title="exercises/dllist/singleton.test.c"
--8<--
exercises/dllist/singleton.test.c
--8<--
```

<!-- ====================================================================== -->

## Add

The `add` and `remove` functions are where it gets a little tricker.
Let's start with `add`. Here is the unannotated version:

```c title="exercises/dllist/add.test.c"
--8<--
exercises/dllist/add.test.c
--8<--
```

_Exercise_: Before reading on, see if you can figure out what
specification is appropriate.

{{ todo("BCP: I seriously doubt they are going to be able to come up
with this specification on their own! We need to set it up earlier
with a simpler example (maybe in a whole earlier section) showing how
to use conditionals in specs. ") }}

Now, here is the annotated version of the `add` operation:

```c title="solutions/dllist/add.test.c"
--8<--
solutions/dllist/add.test.c
--8<--
```

The `requires`
clause is straightforward. We need to own the list centered around
the node that `n` points to. `Before` is a `DlList`
that is either empty, or it has a List to the left,
the current node that `n` points to, and a List to the right.
This corresponds to the state of the list when it is passed in.

In the ensures clause, we again establish ownership of the list, but
this time it is centered around the added node. This means that
`After` is a `DlList` structure similar to `Before`, except that the node
`curr` is now the created node. The old `curr` is pushed into the left
part of the new list. The conditional operator in the `ensures` clause
is saying that if the list was empty coming in, it now is a singleton
list. Otherwise, the left part of the list now has the data from
the old `curr` node, the new `curr` node is the added node, and the
right part of the list is the same as before.

{{ later("BCP: More discussion might be good!") }}


## Remove

Finally, let's look at the `remove` operation. Traditionally, a `remove`
operation for a list returns the integer that was removed. However we
also want all of our functions to return a pointer to the
list. Because of this, we define a `struct` that includes an `int`
and a `node`.

```c title="exercises/dllist/dllist_and_int.test.h"
--8<--
exercises/dllist/dllist_and_int.test.h
--8<--
```

Now we can look at the code for the `remove` operation. Here is the un-annotated version:

```c title="exercises/dllist/remove.test.c"
--8<--
exercises/dllist/remove.test.c
--8<--
```

_Exercise_: Before reading on, see if you can figure out what
specification is appropriate.

{{ todo("BCP: Again, unlikely the reader is going to be able to figure this out without help. We need some hints. ") }}

Now, here is the annotated version of `remove`:

```c title="solutions/dllist/remove.test.c"
--8<--
solutions/dllist/remove.test.c
--8<--
```

Let's look at the pre- and post-conditions. The `requires` clause says that we cannot remove a node from an empty list, so the pointer passed in must not be null. Then we take ownership of the list, and we
assign the node of that list to the identifier `del`
to make our spec more readable. So `Before` refers to the `DlList` when the function is called, and `del` refers to the node that will be deleted.

Then in the `ensures` clause, we must take ownership
of the `node_and_int` struct as well as the `DlList` that
the node is part of. Here, `After` refers to the `DlList`
when the function returns. We ensure that the int that is returned is the value of the deleted node, as intended. Then we have a complicated nested ternary conditional that ensures that `After` is the same as `Before` except for the deleted node. Let's break down this conditional:

- The first guard asks if both `del.prev` and `del.next` are null. In this case, we are removing the only node in the list, so the resulting list will be empty. The `else` branch of this conditional contains its own conditional.

- For the following conditional, the guard checks if `del.prev` is
  _not_ null. This means that the returned node is `del.next`,
  regardless of whether or not `del.prev` is null. If this is the
  case, `After` is now centered around `del.next`, and the left part
  of the list is the same as before. Since `del.next` was previously
  the head of the right side, the right side loses its head in
  `After`. This is where we get `After == DlList{left:
Left_Sublist(Before), curr: Node(After), right: Tl(Right(Before))}`.

- The final `else` branch is the case where `del.next` is null, but
  `del.prev` is not null. In this case, the returned node is
  `del.prev`. This branch follows the same logic as the one before it,
  except now we are taking the head of the left side rather than the
  right side. Now the right side is unchanged, and the left side is just
  the tail, as seen shown in `After == DlList{left:
Tl(Left_Sublist(Before)), curr: Node(After), right: Right(Before)};`

## Exercises

_Exercise_: There are many other functions that one might want to
implement for a doubly linked list. For example, one might want to
implement a function that appends one list to another, or a function
that reverses a list. Try implementing a few of these functions and
writing their specifications.

_Exercise_: For extra practice, try coming up with one or two
variations on the `DlList` data structure itself (there are many!).


