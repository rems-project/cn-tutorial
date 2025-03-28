# Lists, verified

<span style="color:red">
BCP: intro needed
</span>

As before, we need slightly different functions for allocating and
deallocating linked list cells:

```c title="exercises/list/c_types.verif.h"
--8<--
exercises/list/c_types.verif.h
--8<--
```

<span style="color:red">
BCP: Per discussion with Christopher, Cassia, and Daniel, the word "predicate" is quite confusing for newcomers (in logic, predicates do not return things!). A more neutral word might make for significantly easier onboarding.
</span>
<span style="color:red">
Dhruv: Or no keyword? rems-project/cerberus#304 How about traversal?
</span>
<span style="color:red">
 BCP: No keyword sounds even better. But "traversal" in the interim is not bad. Or maybe "extractor" or something like that?
</span>

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

```c title="exercises/list/headers.verif.h"
--8<--
exercises/list/headers.verif.h
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

<span style="color:red">
BCP: Here's the first place where the verification version differs.
Tidy the file above and below!
</span>

Here is a simple destructive `append` function. Note the two uses
of the `unfold` annotation in the body, which are needed to help the
CN typechecker. The `unfold` annotation is an instruction to CN to replace a call to a recursive (CN) function (in this case `append`)
with its definition, and is necessary because CN is unable to automatically determine when and where to expand recursive definitions on its own.

<span style="color:red">
BCP: Can someone add a more technical explanation of why they are needed and exactly what they do?
</span>

```c title="exercises/list/append.verif.c"
--8<--
exercises/list/append.verif.c
--8<--
```

### List copy

Here is an allocating list copy function with a pleasantly light
annotation burden.

```c title="exercises/list/copy.c"
--8<--
exercises/list/copy.c
--8<--
```

### Merge sort

<span style="color:red">
BCP: This could use a gentler explanation (probably in pieces).  But
much of it will be in lists.md, not here.
</span>

Finally, here is a slightly tricky in-place version of merge sort that
avoids allocating any new list cells in the splitting step by taking
alternate cells from the original list and linking them together into
two new lists of roughly equal lengths.

<span style="color:red">
BCP: Nit: Merge multiple requires and ensures clauses into one
</span>

```c title="exercises/list/mergesort.c"
--8<--
exercises/list/mergesort.c
--8<--
```

### Exercises

_Allocating append_. Fill in the CN annotations on
`IntList_append2`. (You will need some in the body as well as at
the top.)

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
