# Allocating and Deallocating Memory

XXXXXXXXXXXXXXXXXXX intro needed

## Block resources

Aside from the `Owned` resources seen so far, CN has another
built-in type of resource called `Block`. Given a C-type `T` and
pointer `p`, `Block<T>(p)` asserts the same ownership as
`Owned<T>(p)` — ownership of a memory cell at `p` the size of type
`T` — but, in contrast to `Owned`, `Block` memory is not assumed
to be initialised.

CN uses this distinction to prevent reads from uninitialised memory:

- A read at C-type `T` and pointer `p` requires a resource
  `Owned<T>(p)`, i.e., ownership of _initialised_ memory at the
  right C-type. The load returns the `Owned` resource unchanged.

- A write at C-type `T` and pointer `p` needs only a
`Block<T>(p)` (so, unlike reads, writes to uninitialised memory
are fine). The write consumes ownership of the `Block` resource
(it destroys it) and returns a new resource `Owned<T>(p)` with the
value written as the output. This means the resource returned from a
write records the fact that this memory cell is now initialised and
can be read from.
<span style="color:red">
BCP: Not sure I understand "returns a new resource `Owned<T>(p)` with the value written as the output" -- perhaps in part because I don't understand what the output of a resource means when the resource is not in the context o a take expression.
</span>

Since `Owned` carries the same ownership as `Block`, just with the
additional information that the `Owned` memory is initalised, a
resource `Owned<T>(p)` is "at least as good" as `Block<T>(p)` —
an `Owned<T>(p)` resource can be used whenever `Block<T>(p)` is
needed. For instance CN’s type checking of a write to `p` requires a
`Block<T>(p)`, but if an `Owned<T>(p)` resource is what is
available, this can be used just the same. This allows an
already-initialised memory cell to be over-written again.

Unlike `Owned`, whose output is the pointee value, `Block` has no meaningful output.

## Allocation

<span style="color:red">
BCP: Again, more text is needed to set up this discussion. Maybe the
first para should move up?
</span>

At the moment, CN does not understand the `malloc` and `free`
functions. They are a bit tricky because they rely on a bit of
polymorphism and a typecast between `char*` -- the result type of
`malloc` and argument type of `free` -- and the actual type of the
object being allocated or deallocated.

However, for any given type, we can define a type-specific function
that allocates heap storage with exactly that type. The
implementation of this function cannot be checked by CN, but we can
give just the spec, together with a promise to link against an
external C library providing a correct (but not verified!) implementation:

```c title="exercises/malloc.h"
--8<--
exercises/malloc.h
--8<--
```

(Alternatively we can include an implementation written in arbitrary C
inside a CN file by marking it with the keyword `trusted` at the top
of its CN specification.)

Similarly:

```c title="exercises/free.h"
--8<--
exercises/free.h
--8<--
```

Now we can write code that allocates and frees memory:

```c title="exercises/slf17_get_and_free.c"
--8<--
exercises/slf17_get_and_free.c
--8<--
```

We can also define a "safer", ML-style version of `malloc` that
handles both allocation and initialization:

```c title="exercises/ref.h"
--8<--
exercises/ref.h
--8<--
```

<span style="color:red">
TODO: BCP: This example is a bit broken: the file `slf0_basic_incr.c` does not appear at all in the tutorial, though a slightly different version (with signed numbers) does...
</span>

```c title="exercises/slf16_basic_succ_using_incr.c"
--8<--
exercises/slf16_basic_succ_using_incr.c
--8<--
```

### Exercises

<span style="color:red">
BCP: There should be a non-ref-using version of this earlier, for comparison. 
</span>

Prove a specification for the following program that reveals _only_
that it returns a pointer to a number that is greater than the number
pointed to by its argument.

```c title="exercises/slf_ref_greater.c"
--8<--
exercises/slf_ref_greater.c
--8<--
```

### Side note

<span style="color:red">
TODO: BCP: This is a bit random -- it's not clear people need to know about this alternate syntax, and it's awkwardly mixed with a semi-interesting example that's not relevant to this section. 
</span>

Here is another syntax for external / unknown
functions, together with an example of a loose specification:

```c title="exercises/slf18_two_dice.c"
--8<--
exercises/slf18_two_dice.c
--8<--
```


