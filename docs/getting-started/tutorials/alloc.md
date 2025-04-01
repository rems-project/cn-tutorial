# Allocating and Deallocating Memory

Our next topic is programs that use dynamically allocated heap memory.

## Malloc and free

Heap-using programs in CN can be written in almost exactly the same
way as in vanilla C.  The only difference is that, instead of calling
`malloc` and `free`, programs should call `cn_malloc` and `cn_free_sized`.
These are CN-specific versions of the usual `malloc` and `free` that
do some testing-related bookkeeping in addition to their main job of
allocating or deallocating heap memory.  The second argument to
`cn_free_sized` is the size of the structure being freed, same as the
argument to `cn_malloc`.

```c title="exercises/cn_malloc.h"
--8<--
exercises/cn_malloc.h
--8<--
```

Using `cn_malloc` and `cn_free`, we can write higher-level programs
that manipulate the heap, as usual.

```c title="exercises/slf17_get_and_free.test.c"
--8<--
exercises/slf17_get_and_free.test.c
--8<--
```
{{ todo("BCP: The `tester` function here does not parse -- not sure why.") }}


### Exercises

Write a specification for the following program that reveals _only_
that it returns a pointer to a number that is greater than the number
pointed to by its argument.

```c title="exercises/slf_greater.test.c"
--8<--
exercises/slf_greater.test.c
--8<--
```

## W resources

In low-level C code, it is sometimes useful to pass around memory that
has been allocated but not yet initialized.  CN provides an alternate
form of resource, written `W`, to address this situation.  Given a
C-type `T` and pointer `p`, `W<T>(p)` asserts the same ownership as
`RW<T>(p)`: ownership of a memory cell at `p` the size of type `T`.
However, but, in contrast to `RW`, `W` memory is not assumed to be
initialised.

CN uses this distinction to prevent reads from uninitialised memory:

- A read at C-type `T` and pointer `p` requires a resource
  `RW<T>(p)`, i.e., ownership of _initialised_ memory at the
  right C-type. The load returns the `RW` resource unchanged.

- A write at C-type `T` and pointer `p` needs only a
  `W<T>(p)` (so, unlike reads, writes to uninitialised memory
  are fine). The write consumes ownership of the `W` resource
  (it destroys it) and returns a new resource `RW<T>(p)` with the
  value written as the output. This means the resource returned from a
  write records the fact that this memory cell is now initialised and
  can be read from.

Since `RW` carries the same ownership as `W`, just with the
additional information that the `RW` memory is initalised, a
resource `RW<T>(p)` is "at least as good" as `W<T>(p)` —
an `RW<T>(p)` resource can be used whenever `W<T>(p)` is
needed. For instance CN’s type checking of a write to `p` requires a
`W<T>(p)`, but if an `RW<T>(p)` resource is what is
available, this can be used just the same. This allows an
already-initialised memory cell to be over-written again.

Unlike `RW`, whose output is the pointee value, `W` has no meaningful output.

{{ todo("BCP: An example and/or an exercise would be nice!") }}
