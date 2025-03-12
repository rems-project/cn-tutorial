# Doubly-linked Lists

<!-- TODO: BCP: The rest of the tutorial (from here to the end) needs to be checked for consistency of naming and capitalization conventions. -->

A doubly linked list is a linked list where each node has a pointer
to both the next node and the previous node. This allows for O(1)
operations for adding or removing nodes anywhere in the list.

Because of all the sharing in this data structure, the separation
reasoning is a bit tricky. We'll give you the core definitions and
then invite you to help fill in the annotations for some of the
functions that manipulate doubly linked lists.

First, here is the C type definition:

```c title="exercises/dll/c_types.h"
--8<--
exercises/dll/c_types.h
--8<--
```

The idea behind the representation of this list is that we don't keep
track of the front or back, but rather we take any node in the list
and have a sequence to the left and to the right of that node. The `left`
and `right` are from the point of view of the node itself, so `left`
is kept in reverse order. Additionally, similarly to in the
`Imperative Queues` example, we can reuse the `List` type.

```c title="exercises/dll/cn_types.h"
--8<--
exercises/dll/cn_types.h
--8<--
```

The predicate for this datatype is a bit complicated. The idea is that
we first own the node that is passed in. Then we follow all of the
`prev` pointers to own everything backwards from the node, and finally
all the `next` pointers to own everything forwards from the node, to
construct the `left` and `right` fields.

<!-- TODO: BCP: Maybe rethink the Own_Forwards / Backwards naming -- would something like Queue_At_Left and Queue_At_Right be clearer?? -->

```c title="exercises/dll/predicates.h"
--8<--
exercises/dll/predicates.h
--8<--
```

Note that `Dll_at` takes ownership of the node passed in, and then
calls `Own_Backwards` and `Own_Forwards`, which recursively take
ownership of the rest of the list.

Also, notice that `Own_Forwards` and `Own_Backwards` include `ptr_eq`
assertions for the `prev` and `next` pointers. This is to ensure that
the nodes in the list are correctly doubly linked. For example, the
line `assert (ptr_eq(n.prev, prev_pointer));` in `Own_Forwards`
ensures that the current node correctly points backward to the
previous node in the list. The line `assert(ptr_eq(prev_node.next,
p));` ensures that the previous node correctly points forward to the
current node.

Before we move on to the functions that manipulate doubly linked
lists, we need to define a few "getter" functions that will allow us
to access the fields of our `Dll` datatype. This will make the
specifications easier to write.

```c title="exercises/dll/getters.h"
--8<--
exercises/dll/getters.h
--8<--
```

We also need some boilerplate for allocation and deallocation.

```c title="exercises/dll/malloc_free.h"
--8<--
exercises/dll/malloc_free.h
--8<--
```

For convenience, we gather all of these files into a single header file.

```c title="exercises/dll/headers.verif.h"
--8<--
exercises/dll/headers.verif.h
--8<--
```

<!-- ====================================================================== -->

Now we can move on to an initialization function. Since an empty list
is represented as a null pointer, we will look at initializing a
singleton list (or in other words, a list with only one item).

```c title="exercises/dll/singleton.c"
--8<--
exercises/dll/singleton.c
--8<--
```

<!-- ====================================================================== -->

The `add` and `remove` functions are where it gets a little tricker.
Let's start with `add`. Here is the unannotated version:

```c title="exercises/dll/add_orig.broken.c"
--8<--
exercises/dll/add_orig.broken.c
--8<--
```

_Exercise_: Before reading on, see if you can figure out what
specification is appropriate and what other are needed.

<!-- TODO: BCP: I rather doubt they are going to be able to come up with this specification on their own! We need to set it up earlier with a simpler example (maybe in a whoile earlier section) showing how to use conditionals in specs. -->

Now, here is the annotated version of the `add` operation:

```c title="exercises/dll/add.c"
--8<--
exercises/dll/add.c
--8<--
```

First, let's look at the pre- and post-conditions. The `requires`
clause is straightforward. We need to own the list centered around
the node that `n` points to. `Before` is a `Dll`
that is either empty, or it has a List to the left,
the current node that `n` points to, and a List to the right.
This corresponds to the state of the list when it is passed in.

In the ensures clause, we again establish ownership of the list, but
this time it is centered around the added node. This means that
`After` is a `Dll` structure similar to `Before`, except that the node
`curr` is now the created node. The old `curr` is pushed into the left
part of the new list. The conditional operator in the `ensures` clause
is saying that if the list was empty coming in, it now is a singleton
list. Otherwise, the left left part of the list now has the data from
the old `curr` node, the new `curr` node is the added node, and the
right part of the list is the same as before.

Now, let's look at the annotations in the function body. CN can
figure out the empty list case for itself, but it needs some help with
the non-empty list case. The `split_case` on `is_null(n->prev)`
tells CN to unpack the `Own_Backwards` predicate. Without this
annotation, CN cannot reason that we didn't lose the left half of the
list before we return, and will claim we are missing a resource for
returning. The `split_case` on `is_null(n->next->next)` is similar,
but for unpacking the `Own_Forwards` predicate. Note that we have to
go one more node forward to make sure that everything past `n->next`
is still owned at the end of the function.

Now let's look at the `remove` operation. Traditionally, a `remove`
operation for a list returns the integer that was removed. However we
also want all of our functions to return a pointer to the
list. Because of this, we define a `struct` that includes an `int`
and a `node`.

```c title="exercises/dll/dllist_and_int.h"
--8<--
exercises/dll/dllist_and_int.h
--8<--
```

Now we can look at the code for the `remove` operation. Here is the un-annotated version:

```c title="exercises/dll/remove_orig.broken.c"
--8<--
exercises/dll/remove_orig.broken.c
--8<--
```

_Exercise_: Before reading on, see if you can figure out what
specification is appropriate and what annotations are needed.

<!-- TODO: BCP: Again, unlikely the reader is going to be able to figure this out without help. We need some hints. -->

Now, here is the fully annotated version of the `remove` operation:

```c title="exercises/dll/remove.c"
--8<--
exercises/dll/remove.c
--8<--
```

First, let's look at the pre- and post-conditions. The `requires` clause says that we cannot remove a node from an empty list, so the pointer passed in must not be null. Then we take ownership of the list, and we
assign the node of that list to the identifier `del`
to make our spec more readable. So `Before` refers to the `Dll` when the function is called, and `del` refers to the node that will be deleted.

Then in the `ensures` clause, we must take ownership
of the `node_and_int` struct as well as the `Dll` that
the node is part of. Here, `After` refers to the `Dll`
when the function returns. We ensure that the int that is returned is the value of the deleted node, as intended. Then we have a complicated nested ternary conditional that ensures that `After` is the same as `Before` except for the deleted node. Let's break down this conditional:

- The first guard asks if both `del.prev` and `del.next` are null. In this case, we are removing the only node in the list, so the resulting list will be empty. The `else` branch of this conditional contains its own conditional.

- For the following conditional, the guard checks if 'del.prev' is
  _not_ null. This means that the returned node is `del.next`,
  regardless of whether or not `del.prev` is null. If this is the
  case, `After` is now centered around `del.next`, and the left part
  of the list is the same as before. Since `del.next` was previously
  the head of the right side, the right side loses its head in
  `After`. This is where we get `After == Dll{left:
Left_Sublist(Before), curr: Node(After), right: Tl(Right(Before))}`.

- The final `else` branch is the case where `del.next` is null, but
  `del.prev` is not null. In this case, the returned node is
  `del.prev`. This branch follows the same logic as the one before it,
  except now we are taking the head of the left side rather than the
  right side. Now the right side is unchanged, and the left side is just
  the tail, as seen shown in `After == Dll{left:
Tl(Left_Sublist(Before)), curr: Node(After), right: Right(Before)};`

The annotations in the function body are similar to in the `add`
function. Both of these `split_case` annotations are needed to unpack
the `Own_Forwards` and `Own_Backwards` predicates. Without them, CN
will not be able to reason that we didn't lose the left or right half
of the list before we return and will claim we are missing a resource
for returning.

<!-- ====================================================================== -->

_Exercise_: There are many other functions that one might want to
implement for a doubly linked list. For example, one might want to
implement a function that appends one list to another, or a function
that reverses a list. Try implementing a few of these functions and
writing their specifications.

_Exercise_: For extra practice, try coming up with one or two
variations on the Dll data structure itself (there are many!).


