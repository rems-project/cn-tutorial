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

```c title="exercises/dllist/add.c"
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

CN can figure out the empty list case for itself, but it needs some
help with the non-empty list case. The `split_case` on
`is_null(n->prev)` tells CN to unpack the `Take_Left`
predicate. Without this annotation, CN cannot reason that we didn't
lose the left half of the list before we return, and will claim we are
missing a resource for returning. The `split_case` on
`is_null(n->next->next)` is similar, but for unpacking the
`Take_Right` predicate. Note that we have to go one more node forward
to make sure that everything past `n->next` is still RW at the end of
the function.

## Remove

Here is the `remove` operation with just its specification:

```c title="exercises/dllist/remove.verif.c"
--8<--
exercises/dllist/remove.verif.c
--8<--
```

_Exercise_: Before reading on, see if you can figure out what
annotations are needed to make CN happy.

Here is the fully annotated version of `remove`:

```c title="solutions/dllist/remove.verif.c"
--8<--
solutions/dllist/remove.verif.c
--8<--
```

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
writing _and verifying_ their specifications.

_Exercise_: For extra practice, try coming up with one or two
variations on the DlList data structure itself (there are many!).


