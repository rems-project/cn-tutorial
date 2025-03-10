# Verification with Pointers to Structured Objects

Verifying CN programs involving structured objects raises a number
of new issues.

## Compound Owned and Block resources

While one might like to think of a struct as a single (compound) object that is manipulated as a whole, C permits more flexible struct manipulation: given a struct pointer, programmers can construct pointers to _individual struct members_ and manipulate these as values, including even passing them to other functions.

CN therefore cannot treat resources for compound C types like structs as primitive, indivisible units. Instead, `Owned<T>` and `Block<T>` are defined inductively on the structure of the C-type `T`.

For struct types `T`, the `Owned<T>` resource is defined as the collection of `Owned` resources for its members (as well as `Block` resources for any padding bytes in-between them). The resource `Block<T>`, similarly, is made up of `Block` resources for all members (and padding bytes).

To handle code that manipulates pointers into parts of a struct object, CN can automatically decompose a struct resource into the member resources, and it can recompose the struct later, as needed. The following example illustrates this.

Recall the function `zero` from our earlier exercise. It takes an `unsigned int` pointer to uninitialised memory, with `Block<unsigned int>` ownership, and initialises the value to zero, returning an `Owned<unsigned int>` resource with output `0`.

Now consider the function `init_point`, shown below, which takes a pointer `p` to a `struct point` and zero-initialises its members by calling `zero` twice, once with a pointer to struct member `x`, and once with a pointer to `y`.

```c title="exercises/init_point.c"
--8<--
exercises/init_point.c
--8<--
```

As stated in its precondition, `init_point` receives ownership `Block<struct point>(p)`. The `zero` function, however, works on `unsigned int` pointers and requires `Block<unsigned int>` ownership.

CN can prove the calls to `zero` with `&p->x` and `&p->y` are safe because it decomposes the `Block<struct point>(p)` into a `Block<unsigned int>` for member `x` and a `Block<unsigned int>` for member `y`. Later, the reverse happens: following the two calls to `zero`, as per `zero`’s precondition, `init_point` has ownership of two adjacent `Owned<unsigned int>` resources – ownership for the two struct member pointers, with the member now initialised. Since the postcondition of `init_point` requires ownership `Owned<struct point>(p)`, CN combines these back into a compound resource. The resulting `Owned<point struct>` resource has for an output the struct value `P_post` that is composed of the zeroed member values for `x` and `y`.

## Resource inference

To handle the required resource inference, CN "`eagerly`" decomposes all `struct` resources into resources for the struct members, and "`lazily`" re-composes them as needed.

We can see this if, for instance, we experimentally change the `transpose` example from above to force a type error. Let’s insert an `/*@ assert(false) @*/` CN assertion in the middle of the `transpose` function, so we can inspect CN’s proof context shown in the error report. (More on CN assertions later.)

<span style="color:red">
BCP: Recheck that what we say here matches what it actually looks like 
</span>

```c title="exercises/transpose.broken.c"
--8<--
exercises/transpose.broken.c
--8<--
```

The precondition of `transpose` asserts ownership of an `Owned<struct point>(p)` resource. The error report now instead lists under "`Available resources`" two resources:

- `Owned<unsigned int>(member_shift<point>(p, x))` with output `P.x` and

- `Owned<unsigned int>(member_shift<point>(p, y))` with output `P.y`

<span style="color:red">
BCP: We should verify that it really does say this. 
</span>

Here `member_shift<s>(p,m)` is the CN expression that constructs, from a `struct s` pointer `p`, the "`shifted`" pointer for its member `m`.

When the function returns, the two member resources are recombined "`on demand`" to satisfy the postcondition `Owned<struct point>(p)`.

### Exercises

_Init point._ Insert CN `assert(false)` statements in different statement positions of `init_point` and check how the available resources evolve.

_Transpose (again)._ Recreate the `transpose` function from before,
using the `swap` function verified earlier.


```c title="exercises/transpose2.c"
--8<--
exercises/transpose2.c
--8<--
```

<span style="color:red">
BCP: Some more things to think about including... 
- Something about CN's version of the frame rule (see
bcp_framerule.c, though the example is arguably a bit unnatural). 
- Examples from Basic.v with allocation - there are lots of
interesting ones!
    CP: Agreed. For now continuing with arrays, but will return to this later.
</span>


