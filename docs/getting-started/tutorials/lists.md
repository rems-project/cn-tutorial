# Lists

Now it's time to look at some more interesting heap structures.

To begin with, here is a C definition for (singly) linked list cells:

```c title="exercises/list/c_types.h"
--8<--
exercises/list/c_types.h
--8<--
```

Here are typed allocation and deallocation functions for this type.
(We provide separate functions for these rather than just calling
`malloc` and `free` directly in the interest of sharing as much code
as possible with the verification-focused variants of these examples.)
{{ later("BCP: ... but maybe we'd get the same amount of sharing if we directly
used malloc?  We should check.") }}

```c title="exercises/list/c_types.test.h"
--8<--
exercises/list/c_types.test.h
--8<--
```

To write specifications for C functions that manipulate lists, we need
to define a CN "predicate" that describes specification-level list
structures. We use the datatype `List` for CN-level lists.

{{ todo(" BCP: Industrial developers will need a _lot_
more help than that!  ") }}

Intuitively, the `SLList_At` predicate walks over a singly-linked
pointer structure in the C heap and extracts an `RW` version of
the CN-level list that it represents.

```c title="exercises/list/cn_types.h"
--8<--
exercises/list/cn_types.h
--8<--
```

We can also write _functions_ on CN-level lists by ordinary functional
programming (in a slightly strange, unholy-union-of-C-and-Rust
syntax):

```c title="exercises/list/hdtl.h"
--8<--
exercises/list/hdtl.h
--8<--
```

We use the `SLList_At` predicate to specify functions returning the
empty list and the cons of a number and a list.

```c title="exercises/list/constructors.h"
--8<--
exercises/list/constructors.h
--8<--
```

Finally, we can collect all this stuff into a single header file. (We
add the usual C `#ifndef` gorp to avoid complaints from the compiler
if it happens to get included twice from the same source file later.)

```c title="exercises/list/headers.test.h"
--8<--
exercises/list/headers.test.h
--8<--
```

### Append

With this basic infrastructure in place, we can start specifying and
verifying list-manipulating functions. First, `append`.

Here is its specification (in a separate file, because we'll want to
use it multiple times below).

```c title="exercises/list/append.h"
--8<--
exercises/list/append.h
--8<--
```

Here is a simple destructive `append` function.

```c title="exercises/list/append.test.c"
--8<--
exercises/list/append.test.c
--8<--
```

### List copy

Here is an allocating list copy function.

```c title="exercises/list/copy.c"
--8<--
exercises/list/copy.c
--8<--
```

### Merge sort

{{ todo(" BCP: This could use a gentler explanation
(probably broken in pieces) We've heard from more than one reader that this
example is particularly hard to digest without some additional help") }}

Finally, here is a slightly tricky in-place version of merge sort that
avoids allocating any new list cells in the splitting step by taking
alternate cells from the original list and linking them together into
two new lists of roughly equal lengths.

```c title="exercises/list/mergesort.test.c"
--8<--
exercises/list/mergesort.test.c
--8<--
```

### Exercises

_Exercise_. Fill in an appropriate specification for
`IntList_append2`.

```c title="exercises/list/append2.test.c"
--8<--
exercises/list/append2.test.c
--8<--
```

Note that it would not make sense to do the usual
functional-programming trick of copying xs but sharing ys. (Why?)

_Exercise_. Add annotations to the `length` function as appropriate:

```c title="exercises/list/length.c"
--8<--
exercises/list/length.c
--8<--
```

_Exercise_. Fill in the body of the following list deallocation
procedure and add annotations as appropriate:

```c title="exercises/list/free.c"
--8<--
exercises/list/free.c
--8<--
```

_Exercise_. Add a specification to the following "`length` with an
accumulator" function:

{{ todo("BCP: move the file!") }}

```c title="exercises/slf_length_acc.c"
--8<--
exercises/slf_length_acc.c
--8<--
```
