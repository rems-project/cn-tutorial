# Lists

<span style="color:red">
BCP: Maybe this should be a case study?
</span>

<span style="color:red">
BCP: Better intro needed
</span>

Now it's time to look at some more interesting heap structures.

To begin with, here is a C definition for linked list cells, together
with allocation and deallocation functions:

<span style="color:red">
BCP: break sllist out into its own separate .h file and look at it first
</span>

```c title="exercises/list/c_types.test.h"
--8<--
exercises/list/c_types.test.h
--8<--
```

To write specifications for C functions that manipulate lists, we need
to define a CN "predicate" that describes specification-level list
structures, as one would do in ML, Haskell, or Coq. We use the
datatype `List` for CN-level lists.

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
<span style="color:red">
BCP: Surely we've made that point already?
</span>


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

<span style="color:red">
TODO: BCP: The 'return != NULL' should not be needed, but to remove it
we need to change the callers of all the allocation functions to check
for NULL and exit (which requires adding a spec for exit).
</span>

### Append

With this basic infrastructure in place, we can start specifying and
verifying list-manipulating functions. First, `append`.

Here is its specification (in a separate file, because we'll want to
use it multiple times below.)

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

<span style="color:red">
BCP: `L_` should probably be `L_post`
</span>

```c title="exercises/list/copy.c"
--8<--
exercises/list/copy.c
--8<--
```

### Merge sort

<span style="color:red"> BCP: This could use a gentler explanation
(probably in pieces) We've heard from more than one reader that this
example is particularly hard to digest without some additional help
</span>

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

_Allocating append_. Fill in an appropriate specification for
`IntList_append2`.

```c title="exercises/list/append2.c"
--8<--
exercises/list/append2.c
--8<--
```

Note that it would not make sense to do the usual
functional-programming trick of copying xs but sharing ys. (Why?)

_Length_. Add annotations as appropriate:

```c title="exercises/list/length.c"
--8<--
exercises/list/length.c
--8<--
```

_List deallocation_. Fill in the body of the following procedure and
add annotations as appropriate:

```c title="exercises/list/free.c"
--8<--
exercises/list/free.c
--8<--
```

_Length with an accumulator_. Add annotations as appropriate:

<span style="color:red">
BCP: Removing / forgetting the unfold in this one gives a truly
</span>
<span style="color:red">
 bizarre error message saying that the constraint "n == (n + length(L1))"
</span>
<span style="color:red">
 is unsatisfiable...
</span>

<span style="color:red">
Sainati: when I went through the tutorial, the file provided for this exercise was already "complete" in that
</span>
<span style="color:red">
 it already had all the necessary annotations present for CN to verify it
</span>

```c title="exercises/slf_length_acc.c"
--8<--
exercises/slf_length_acc.c
--8<--
```
