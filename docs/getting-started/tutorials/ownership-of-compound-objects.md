# Ownership of Compound Objects

So far, our examples have worked with just integers and pointers, but larger programs typically also manipulate compound values, often represented using C struct types. Specifying functions manipulating structs works in much the same way as with basic types.

For instance, the following example uses a `struct` `point` to represent a point in two-dimensional space. The function `transpose` swaps a point’s `x` and `y` coordinates.

```c title="exercises/transpose.c"
--8<--
exercises/transpose.c
--8<--
```

Here the precondition asserts ownership for `p`, at type `struct
point`; the output `P_post` is a value of CN type `struct point`,
i.e. a record with members `i32` `x` and `i32` `y`. The
postcondition similarly asserts ownership of `p`, with output
`P_post`, and asserts the coordinates have been swapped, by referring to
the members of `P` and `P_post` individually.

<!-- TODO: BCP: This paragraph is quite confusing if read carefully: it seems to say that the "take" in the requires clause returns a different type than the "tajke" in the "ensures" clause. Moreover, even if the reader decides that this cannot be the case and they have to return the same type, they may wonder whether thius type is a C type (which is what it looks like, since there is only one struct declaration, and it is not in a magic comment) or a CN type (which might be expected, since it is the result of a "take"). I _guess_ what's going on here is that every C type is automatically reflected as a CN type with the same name. But this story is also not 100% satisfying, since the basic numeric types don't work this way: each C numeric type has an _analog_ in CN, but with a different name. -->

<!--
-- Dhruv:
C supports strong updates in certain situations and so take _ = Owned<ct>(p) in the requires clause could very well have a different C type than take _ = Owned<ct2>(p) in the ensures clause.

The reason Owned needs a C-type is so that it can (a) figure out the size of the sub-heap being claimed and (b) figure out how one may need to destructure the type (unions, struct fields and padding, arrays). The relationship is that for take x = Owned<ct>(expr), expr : pointer, x : to_basetype(ct).

There is a design decision to consider here rems-project/cerberus#349
-->

### Compound Owned and Block resources

While one might like to think of a struct as a single (compound) object that is manipulated as a whole, C permits more flexible struct manipulation: given a struct pointer, programmers can construct pointers to _individual struct members_ and manipulate these as values, including even passing them to other functions.

CN therefore cannot treat resources for compound C types like structs as primitive, indivisible units. Instead, `Owned<T>` and `Block<T>` are defined inductively on the structure of the C-type `T`.

For struct types `T`, the `Owned<T>` resource is defined as the collection of `Owned` resources for its members (as well as `Block` resources for any padding bytes in-between them). The resource `Block<T>`, similarly, is made up of `Block` resources for all members (and padding bytes).

To handle code that manipulates pointers into parts of a struct object, CN can automatically decompose a struct resource into the member resources, and it can recompose the struct later, as needed. The following example illustrates this.

Recall the function `zero` from our earlier exercise. It takes an `int` pointer to uninitialised memory, with `Block<int>` ownership, and initialises the value to zero, returning an `Owned<int>` resource with output `0`.

Now consider the function `init_point`, shown below, which takes a pointer `p` to a `struct point` and zero-initialises its members by calling `zero` twice, once with a pointer to struct member `x`, and once with a pointer to `y`.

```c title="exercises/init_point.c"
--8<--
exercises/init_point.c
--8<--
```

As stated in its precondition, `init_point` receives ownership `Block<struct point>(p)`. The `zero` function, however, works on `int` pointers and requires `Block<int>` ownership.

CN can prove the calls to `zero` with `&p->x` and `&p->y` are safe because it decomposes the `Block<struct point>(p)` into a `Block<int>` for member `x` and a `Block<int>` for member `y`. Later, the reverse happens: following the two calls to `zero`, as per `zero`’s precondition, `init_point` has ownership of two adjacent `Owned<int>` resources – ownership for the two struct member pointers, with the member now initialised. Since the postcondition of `init_point` requires ownership `Owned<struct point>(p)`, CN combines these back into a compound resource. The resulting `Owned<point struct>` resource has for an output the struct value `P_post` that is composed of the zeroed member values for `x` and `y`.

### Resource inference

To handle the required resource inference, CN "`eagerly`" decomposes all `struct` resources into resources for the struct members, and "`lazily`" re-composes them as needed.

We can see this if, for instance, we experimentally change the `transpose` example from above to force a type error. Let’s insert an `/*@ assert(false) @*/` CN assertion in the middle of the `transpose` function, so we can inspect CN’s proof context shown in the error report. (More on CN assertions later.)

<!-- TODO: BCP: Recheck that what we say here matches what it actually looks like -->

```c title="exercises/transpose.broken.c"
--8<--
exercises/transpose.broken.c
--8<--
```

The precondition of `transpose` asserts ownership of an `Owned<struct point>(p)` resource. The error report now instead lists under "`Available resources`" two resources:

- `Owned<signed int>(member_shift<point>(p, x))` with output `P.x` and

- `Owned<signed int>(member_shift<point>(p, y))` with output `P.y`

<!-- TODO: BCP: We should verify that it really does say this. -->

Here `member_shift<s>(p,m)` is the CN expression that constructs, from a `struct s` pointer `p`, the "`shifted`" pointer for its member `m`.

When the function returns, the two member resources are recombined "`on demand`" to satisfy the postcondition `Owned<struct point>(p)`.

### Exercises

_Init point._ Insert CN `assert(false)` statements in different statement positions of `init_point` and check how the available resources evolve.

_Transpose (again)._ Recreate the transpose function from before, now using the swap function verified earlier (for `struct upoint`, with unsigned member values).

```c title="exercises/transpose2.c"
--8<--
exercises/transpose2.c
--8<--
```

<!--
TODO: BCP: Some more things to think about including... - Something about CN's version of the frame rule (see
bcp_framerule.c, though the example is arguably a bit
unnatural). - Examples from Basic.v with allocation - there are lots of
interesting ones!
CP: Agreed. For now continuing with arrays, but will return to this later.
-->


