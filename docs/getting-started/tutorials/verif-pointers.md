# Verification with Pointers to Structured Objects

Verifying CN programs involving structured objects raises a number
of new issues.

## Compound RW resources

Given a struct pointer, C programmers can construct pointers to _individual struct members_ and manipulate these as values, including even passing them to other functions. CN therefore cannot treat resources for compound C types like structs as indivisible units.

Instead, `RW<T>` is defined inductively on the structure of the C-type `T`.
To handle code that manipulates pointers into parts of a struct object, CN can automatically decompose a struct resource into the resources of its members, and it can recompose the struct later, as needed. The following example illustrates this.

Suppose we have a function `zero` that initializes a pointer to 0. Now consider the function `init_point` which takes a pointer `p` to a `struct point` and zero-initialises its members by calling `zero` twice, once with a pointer to struct member `x`, and once with a pointer to `y`.

```c title="exercises/init_point.c"
--8<--
exercises/init_point.c
--8<--
```

As stated in its precondition, `init_point` receives ownership `RW<struct point>(p)`. The `zero` function, however, works on `unsigned int` pointers and requires `RW<unsigned int>` ownership.

CN can prove the calls to `zero` with `&p->x` and `&p->y` are safe because it decomposes the `RW<struct point>(p)` into a `RW<unsigned int>` for member `x` and likewise for member `y`. Later, the reverse happens. Since the postcondition of `init_point` requires ownership `RW<struct point>(p)`, CN combines these back into a compound resource. The resulting pointee value `P_post` is a struct composed of the zeroed member values for `x` and `y`.

## Resource inference

To handle the required resource inference, CN "`eagerly`" decomposes all `struct` resources into resources for the struct members, and "`lazily`" re-composes them as needed.

We can see this if we experimentally change the previous `transpose` example to force a type error. Let’s insert an `/*@ assert(false) @*/` CN assertion in the middle of `transpose`, so we can inspect CN’s proof context shown in the error report. (More on CN assertions later.)

<span style="color:red">
BCP: Recheck that what we say here matches what it actually looks like
</span>
<span style="color:red">
JWS: It appears quite different now. Seems like we can now step through the function (so is the assert still necessary?)
and the `Available resources` at the assert line are
RW<unsigned int>(&temp_y)(P.y)
RW<unsigned int>(&temp_x)(P.x)
RW<struct point*>(&ARG0)(p)
RW<unsigned int>(&p->y)(P.y)
RW<unsigned int>(&p->x)(P.x)
...I would just edit the text but I'm not sure how this output aligns with the one described below
</span>
<span style="color:red">
BCP: Someone just needs to look at it carefully and write down what's
true. I've lost track. :-)
</span>

```c title="exercises/transpose.broken.c"
--8<--
exercises/transpose.broken.c
--8<--
```

The precondition of `transpose` asserts ownership of an `RW<struct point>(p)` resource. The error report now instead lists under "`Available resources`" two resources:

- `RW<unsigned int>(member_shift<point>(p, x))` with output `P.x` and

- `RW<unsigned int>(member_shift<point>(p, y))` with output `P.y`

<span style="color:red">
BCP: We should verify that it really does say this.   (It certainly
does not, after recent syntax changes...)
</span>

Here `member_shift<s>(p,m)` is the CN expression that constructs, from a `struct s` pointer `p`, the "`shifted`" pointer for its member `m`.

When the function returns, the two member resources are recombined "`on demand`" to satisfy the postcondition `RW<struct point>(p)`.

### Exercises

_Exercise:_ Insert CN `assert(false)` statements in different statement positions of `init_point` and check how the available resources evolve.

_Exercise:_  Recreate the `transpose` function from before, now
using the `swap` function.
<span style="color:red">
JWS: What exactly is it that they're supposed to do here? Seems like just copy-pasting the specification from above will work?
</span>
<span style="color:red">
BCP: Maybe that's OK?  Or maybe we can think of a more interesting variant...
</span>


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
    CP: Agreed. For now continuing with arrays, but will return to this later.
") }}


