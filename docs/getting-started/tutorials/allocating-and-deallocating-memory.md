# Allocating and Deallocating Memory

<!-- TODO: BCP: Again, more text is needed to set up this discussion. -->

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

<!--
TODO: BCP: This example is a bit broken: the file `slf0_basic_incr.c` does not appear at all in the tutorial, though a slightly different version (with signed numbers) does...
-->

```c title="exercises/slf16_basic_succ_using_incr.c"
--8<--
exercises/slf16_basic_succ_using_incr.c
--8<--
```

### Exercises

<!-- TODO: BCP: There should be a non-ref-using version of this earlier, for comparison. -->

Prove a specification for the following program that reveals _only_
that it returns a pointer to a number that is greater than the number
pointed to by its argument.

```c title="exercises/slf_ref_greater.c"
--8<--
exercises/slf_ref_greater.c
--8<--
```

### Side note

Here is another syntax for external / unknown
functions, together with an example of a loose specification:

<!--
TODO: BCP: This is a bit random -- it's not clear people need to know about this alternate syntax, and it's awkwardly mixed with a semi-interesting example that's not relevant to this section. Also awkwardly placed, right here.
-->

```c title="exercises/slf18_two_dice.c"
--8<--
exercises/slf18_two_dice.c
--8<--
```


