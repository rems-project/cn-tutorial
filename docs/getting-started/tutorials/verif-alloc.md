# Allocating and Deallocating Memory, Verified

## Verifying programs with malloc and free

Verifying programs that allocate and deallocate heap memory is a bit
different from testing such programs, in two respects:

On one hand, there is no need to link against the nonstandard
`cn_malloc` and `cn_free` functions: programs can just use the
standard `malloc` and `free`.

However, at the moment, CN's verification machinery does not
understand the types of the `malloc` and `free` functions, which are a
bit tricky because they rely on a bit of polymorphism and a typecast
between `char*` -- the result type of `malloc` and argument type of
`free` -- and the actual type of the object being allocated or
deallocated.

To work around this shortcoming, verifying programs with heap
allocation can follow one of two strategies.

### First strategy

The simplest way to allocate and free storage is to define custom
allocation and deallocation functions for each type that might be
stored in the heap.  These are defined as `extern`s, with no bodies,
which instructs CN just to trust their specifications.

```c title="exercises/malloc.h"
--8<--
exercises/malloc.h
--8<--
```

```c title="exercises/free.h"
--8<--
exercises/free.h
--8<--
```

```c title="exercises/slf17_get_and_free.verif.c"
--8<--
exercises/slf17_get_and_free.verif.c
--8<--
```

### Second strategy

Alternatively we can include an actual implementation of
`malloc__unsigned_int` and `free__unsigned_int` written in arbitrary C
inside a CN file by marking them with the keyword `trusted` at the top
of their CN specifications.

<span style="color:red">
BCP: Make up a real example...
</span>

```c title="exercises/malloc_trusted.verif.c"
--8<--
exercises/malloc_trusted.verif.c
--8<--
```
