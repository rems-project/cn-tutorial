# Allocating and deallocating memory, verified


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

### Exercises

_Exercise:_ This specification is broken. (Run `cn verify` to see the error
message.) Fix the specification by fixing which kinds of resources are used.

```c title="exercises/w_resources_ex.broken.c"
--8<--
exercises/w_resources_ex.broken.c
--8<--
```

## Verifying programs with malloc and free

Verifying programs that allocate and deallocate heap memory is a bit
different from testing such programs, in two respects:

On one hand, there is no need to link against the nonstandard
`cn_malloc` and `cn_free_sized` functions: programs can just use the
standard `malloc` and `free`.

However, at the moment, CN's verification machinery does not
understand the types of the `malloc` and `free` functions, which are a
bit tricky because they rely on a bit of polymorphism and a typecast
between `char*` — the result type of `malloc` and argument type of
`free` — and the actual type of the object being allocated or
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

{{ todo("BCP: Make up a real example...") }}

```c title="exercises/malloc_trusted.verif.c"
--8<--
exercises/malloc_trusted.verif.c
--8<--
```
{{ todo("JWS: Where is this file?") }}
