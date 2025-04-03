# Doubly-linked Lists, Verified

Verifying the doubly-linked list operations requires a few extra
annotations. 

The basic definitions are unchanged from the associated testing
chapter, except that as usual we need some boilerplate for allocation and deallocation.

```c title="exercises/dllist/allocation.verif.h"
--8<--
exercises/dllist/allocation.verif.h
--8<--
```

<!-- ====================================================================== -->

## Singleton

The `singleton` function can be verified by CN with no additional annotations.

```c title="exercises/dllist/singleton.verif.c"
--8<--
exercises/dllist/singleton.verif.c
--8<--
```

<!-- ====================================================================== -->

## Add

The `add` and `remove` functions are where it gets a little tricker.
Let's start with `add`.  Here is a version with just the pre- and
post-condition as in the testing version of this chapter:

```c title="exercises/dllist/add_orig.broken.c"
--8<--
exercises/dllist/add.c
--8<--
```

_Exercise_: Before reading on, see if you can figure out what
annotations need to be added to the body of the function to make CN
accept it.

Here is the fully annotated version:

```c title="solutions/dllist/add.c"
--8<--
solutions/dllist/add.c
--8<--
```

## Remove

Let's look at the required annotations in the function body. CN can
figure out the empty list case for itself, but it needs some help with
the non-empty list case. The `split_case` on `is_null(n->prev)`
tells CN to unpack the `Take_Left` predicate. Without this
annotation, CN cannot reason that we didn't lose the left half of the
list before we return, and will claim we are missing a resource for
returning. The `split_case` on `is_null(n->next->next)` is similar,
but for unpacking the `Take_Right` predicate. Note that we have to
go one more node forward to make sure that everything past `n->next`
is still RW at the end of the function.

Now let's look at the `remove` operation. Traditionally, a `remove`
operation for a list returns the integer that was removed. However we
also want all of our functions to return a pointer to the
list. Because of this, we define a `struct` that includes an `int`
and a `node`.

```c title="exercises/dllist/dllist_and_int.h"
--8<--
exercises/dllist/dllist_and_int.h
--8<--
```

Now we can look at the code for the `remove` operation. Here is the un-annotated version:

```c title="exercises/dllist/remove_orig.broken.c"
--8<--
exercises/dllist/remove_orig.broken.c
--8<--
```

_Exercise_: Before reading on, see if you can figure out what
specification is appropriate and what annotations are needed.

{{ todo("BCP: Again, unlikely the reader is going to be able to figure this out without help. We need some hints. ") }}

Now, here is the fully annotated version of the `remove` operation:

```c title="exercises/dllist/remove.c"
--8<--
exercises/dllist/remove.c
--8<--
```

First, let's look at the pre- and post-conditions. The `requires` clause says that we cannot remove a node from an empty list, so the pointer passed in must not be null. Then we take ownership of the list, and we
assign the node of that list to the identifier `del`
to make our spec more readable. So `Before` refers to the `DlList` when the function is called, and `del` refers to the node that will be deleted.

Then in the `ensures` clause, we must take ownership
of the `node_and_int` struct as well as the `DlList` that
the node is part of. Here, `After` refers to the `DlList`
when the function returns. We ensure that the int that is returned is the value of the deleted node, as intended. Then we have a complicated nested ternary conditional that ensures that `After` is the same as `Before` except for the deleted node. Let's break down this conditional:

- The first guard asks if both `del.prev` and `del.next` are null. In this case, we are removing the only node in the list, so the resulting list will be empty. The `else` branch of this conditional contains its own conditional.

- For the following conditional, the guard checks if 'del.prev' is
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

The annotations in the function body are similar to in the `add`
function. Both of these `split_case` annotations are needed to unpack
the `Take_Right` and `Take_Left` predicates. Without them, CN
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
variations on the DlList data structure itself (there are many!).


