# Lists, verified

Now let's see what's needed to fully verify linked-list operations.

The basic definitions collected in the file `lists/headers.verif.h`
are pretty much the same as for the testing version of lists.  The
only difference is that, as before, we need to define slightly
different functions for allocating and deallocating linked list cells.

### Append

The specification of `append` is identical to the testing
version:

```c title="exercises/list/append.h"
--8<--
exercises/list/append.h
--8<--
```

And here is the verified code for a simple destructive implementation
of `append`.  Note the two uses of the `unfold` annotation in the
body, which are needed to help the CN typechecker. This annotation is
an instruction to CN to replace a call to a recursive (CN) function
(in this case `append`) with its definition, and is necessary because
CN is unable to automatically determine when and where to expand
recursive definitions on its own.

{{ todo("BCP: Can someone add a more technical explanation of why they are needed and exactly what they do?") }}

```c title="exercises/list/append.verif.c"
--8<--
exercises/list/append.verif.c
--8<--
```

### List copy

The verified version of the list copy function is identical to the
testing version.  No additional annotations are needed.

### Merge sort

Finally, here is in-place mergesort, with all necessary `unfold`
annotations so that it is accepted by the CN verifier.

```c title="solutions/list/mergesort.verif.c"
--8<--
solutions/list/mergesort.verif.c
--8<--
```

### Exercises

_Exercise_. Fill in the CN annotations on the `IntList_append2`
function below. (You will need some in the body as well as at the
top.)

```c title="exercises/list/append2.c"
--8<--
exercises/list/append2.c
--8<--
```

_Exercise_. Add annotations to `length` as appropriate:

```c title="exercises/list/length.c"
--8<--
exercises/list/length.c
--8<--
```

_Exercise_. Fill in the body of the following list deallocation
function and add annotations as appropriate:

```c title="exercises/list/free.c"
--8<--
exercises/list/free.c
--8<--
```

_Exercise_. Add annotations as appropriate:

{{ later("BCP: Removing / forgetting the unfold in this one gives a
truly bizarre error message saying that the constraint `n == (n +
length(L1))` is unsatisfiable...") }}

```c title="exercises/slf_length_acc.c"
--8<--
exercises/slf_length_acc.c
--8<--
```
