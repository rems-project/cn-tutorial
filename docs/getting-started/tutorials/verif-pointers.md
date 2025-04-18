# Pointers to structured objects, verified

Verifying CN programs involving structured objects raises a number
of new issues.

## Compound RW resources

Given a struct pointer, C programmers can construct pointers to _individual struct members_ and manipulate these as values, including even passing them to other functions. CN therefore cannot treat resources for compound C types like structs as indivisible units.

Instead, `RW<T>` is defined inductively on the structure of the C-type `T`.
To handle code that manipulates pointers into parts of a struct object, CN can automatically decompose a struct resource into the resources of its members, and it can recompose the struct later, as needed. The following example illustrates this.

Suppose we have a function `zero` that takes a pointer to an `unsigned int` and initialises its value to 0. Now consider the function `init_point` which takes a pointer `p` to a `struct point` and zero-initialises its members by calling `zero` twice, once with a pointer to struct member `x`, and once with a pointer to `y`.

```c title="exercises/init_point.c"
--8<--
exercises/init_point.c
--8<--
```

As stated in its precondition, `init_point` receives ownership `RW<struct point>(p)`. The `zero` function, however, works on `unsigned int` pointers and requires ownership `RW<unsigned int>`, so CN cannot simply pass `init_point`'s struct ownership to `zero`. Instead, CN decomposes the `RW<struct point>(p)` resource into two `RW<unsigned int>` resources, one for each member pointer, and proves that the calls to `zero` with `&p->x` and `&p->y` are safe by supplying the respective `RW<unsigned int>` resources.

Later, the reverse happens. Since the postcondition of `init_point` requires ownership `RW<struct point>(p)`, CN re-assembles the two `RW<unsigned int>` resources (now both zero-initialised) back into a compound struct resource. The resulting pointee value `P_post` is a struct composed of the zeroed member values for `x` and `y`.

## Resource inference

To handle the required resource inference, CN "eagerly" decomposes all `struct` resources into resources for the struct members, and "lazily" re-composes them as needed.

We can see this if we experimentally change the previous `transpose` example to force a verification error. Let’s insert an `/*@ assert(false); @*/` CN assertion into the middle of `transpose`, so we can inspect CN’s proof context shown in the error report. (More on CN assertions later.)

<!-- {{ todo("BCP: Recheck that what we say here matches what it actually looks like") }}
{{ todo("JWS: It appears quite different now. Seems like we can now step through the function (so is the assert still necessary?)
and the `Available resources` at the assert line are
RW<unsigned int>(&temp_y)(P.y)
RW<unsigned int>(&temp_x)(P.x)
RW<struct point*>(&ARG0)(p)
RW<unsigned int>(&p->y)(P.y)
RW<unsigned int>(&p->x)(P.x)
...I would just edit the text but I'm not sure how this output aligns with the one described below") }}
{{ todo("BCP: Someone just needs to look at it carefully and write down what's
true. I've lost track. :-)") }} -->

```c title="exercises/transpose.broken.c"
--8<--
exercises/transpose.broken.c
--8<--
```

CN produces an HTML error report with information about a possible trace of the function leading to the error. Click 'last' to jump to the state just before the error. Under "`Available resources`" we find five resources listed. The first three capture ownership of the local variables:
- `RW<unsigned int>(&temp_y)(P.y)` (ownership of the stack location holding local variable `temp_y`)
- `RW<unsigned int>(&temp_x)(P.x)` (as above, for `temp_x`)
- `RW<struct point*>(&ARG0)(p)` (ownership of the stack location holding the value of function argument `p`). More relevant for us now, the remaining two resources contain the `struct point` ownership. Whereas in the precondition of `transpose` we asserted ownership of an `RW<struct point>(p)` resource, here we instead see that CN has decomposed this into the two member resources:
- `RW<unsigned int>(&p->y)(P.y)` (asserting ownership of location `&p->y`, and that the value is the `y` member of the input struct value `P`)
- `RW<unsigned int>(&p->x)(P.x)` (respectively asserting ownership of `&p->x` with value `P.x`).

<!-- {{ todo("BCP: We should verify that it really does say this.   (It certainly
does not, after recent syntax changes...)") }} -->

<!-- Here `member_shift<s>(p,m)` is the CN expression that constructs, from a `struct s` pointer `p`, the "`shifted`" pointer for its member `m`. -->

The assignments to `p->x` and `p->y` update these member resources with new values, and when the function returns, they are recombined "`on demand`" to satisfy the postcondition `RW<struct point>(p)`.

### Exercises

_Exercise:_ Insert CN `assert(false)` statements in different statement positions of `init_point` and check how the available resources evolve.

_Exercise:_  Recreate the `transpose` function from before, now
using the `swap` function: write a specification for `swap` (as defined below) and verify the result in CN.
{{ todo("JWS: What exactly is it that they're supposed to do here? Seems like just copy-pasting the specification from above will work?") }}
{{ todo("BCP: Maybe that's OK?  Or maybe we can think of a more interesting variant...") }}
{{ todo("CP: I tweaked the exercise so it includes (at least) giving a specification for `swap`; that's still an easy exercise and we could use more+more interesting ones, but maybe it's better than nothing, for now.") }}


```c title="exercises/transpose2.c"
--8<--
exercises/transpose2.c
--8<--
```

{{ later(" BCP: Some more things to think about including...
- Something about CN's version of the frame rule (see
bcp_framerule.c, though the example is arguably a bit unnatural).
- Examples from Basic.v with allocation - there are lots of
interesting ones!
    CP: Agreed. For now continuing with arrays, but will return to this later.") }}


