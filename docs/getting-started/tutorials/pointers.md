# Pointers and Simple Ownership

<span style="color:blue">JWS is in the middle of editing this section</span>

<!--
    Rough notes / updated outline:

    - read.c
        - unannotated version fails tests
             - need to explain how to figure out WHY testing fails!
        - explain ownership (copy/move from verification tutorial)
        - version with proper spec works better!
        - read.broken.c demonstrates linearity of resource usage
    - exercises:
        - quadruple_mem
        - abs_mem (this doesn't work with unsigned ints, but we can
          use the other examples from the previous section)
    - slf0_basic_incr_signed.c
        shows the difference between Block and Owned
    - exercises
        - zero.c
        - basic_inplace_double.c involves UB, so skip it or (maybe
          better) replace with something that doesn't
        - maybe something about swapping pointers?

    - add_read  (but changing it to swapping or something, to avoid UB
      issues)

    - everything up through pointers to compound objects seems to work
      well, except for some of the resource inference stuff-->

So far we’ve only considered functions manipulating numeric
values. Specifications become more interesting when _pointers_ are
involved, because the safety of memory accesses via pointers has to be
taken into account.

CN uses _separation logic resources_ and the concept of _ownership_ to
reason about memory accesses. A _resource_, intuitively, represents
the permission to access a region of memory.

Let’s look at a simple example. The function `read` takes an integer
pointer `p` and returns the pointee value.

```c title="exercises/read.c"
--8<--
exercises/read.c
--8<--
```

Running `cn test` on this example produces an error that looks like this:

```
Testing read::read:
FAILED
function read, file ./read-exec.c, line 18
************************************************************
function read, file ./read-exec.c, line 18
Load failed.
  ==> 0x122592a09[0] (0x122592a09) not owned
```

For the read `*p` to be safe, we need to know that the function has permission
to access the memory pointed to by `p`. We next explain how to represent this
permission.

## Owned resources

Given a C-type `T` and pointer `p`, the resource `Owned<T>(p)` asserts
_ownership_ of a memory region at location `p` of the size of the C type
`T`.

<!-- If `T` is a single-word type, then `<T>` can be omitted. -->
<!-- JWS: ^I propose that we cut this sentence, since
I don't know what a "single-word type" is and
I think type annotations that are sometimes optional and sometimes not
are less confusingly presented as always required? -->

<!-- BCP: I feel torn about this.  On one hand, the CN specs we are
     asking people to read and write are pretty long and verbose,
     impeding understanding, and removing all these type annotations
     would streamline some of them significantly.  Moreover, I don't
     find it hard to explain to a C programmer that when the type is
     represented in 32 bits it can be omitted.  On the other hand, I
     do agree that there is *some* overhead to telling people that the
     annotation can be omitted. I can see a couple stable alternatives:
       - Keep the annotations everywhere
       - Delete them everywhere they can be deleted (i.e., for
         one-word types) and explain, either here or when we get to the
         first multi-word pointer target, that we need the annotation
         there.
     I mildly prefer the second. But I wonder whether the decision
     should be informed by some data about whether pointers to single
     words are common in real C code...
-->

<!-- TODO: BCP: Do we mean 32-bit word here?? -->
<!-- TODO: BCP: Maybe the description of the T argument can be
     postponed for a while, if we remove the <unsigned int>
     annotations...? -->

In this example, we can ensure the safe execution of `read` by adding
a precondition that requires ownership of `Owned<unsigned int>(p)`, as
shown below. (The `take ... =` part will be explained shortly.) Since
reading the pointer does not disturb its value,
we can also add a corresponding postcondition, whereby `read` returns
ownership of `p` after it is finished executing, in the form of
another `Owned<unsigned int>(p)` resource.

```c title="solutions/read.c"
--8<--
solutions/read.c
--8<--
```

This specification can be read as follows:

- any function calling `read` has to be able to provide a resource
  `Owned<unsigned int>(p)` to pass into `read`, and

- the caller will receive back a resource `Owned<unsigned int>(p)` when
  `read` returns.

## Pointee values

In addition to reasoning about memory accesed by pointers, we likely also want
to reason about the actual values that the pointers point to. The `take P =` in
the precondition assigns the name `P` to the pointee value of `p`.

That means we can use the pointee values from the pre- and postcondition to
strengthen the specification of `read`. We add two new postconditions specifying

1. that `read` returns `P`, the initial pointee value of `p`, and
1. that the pointee values `P` and `P_post` before and after execution of `read` (respectively) are the same.

```c title="exercises/read2.c"
--8<--
exercises/read2.c
--8<--
```

??? note "Aside (for separation-logic experts)"
    _Aside._ In standard separation logic, the equivalent specification for `read` could have been phrased as follows (where `\return` binds the return value in the postcondition):

    <span style="color:red">
    Sainati: as a separation logic noob, I would love a more detailed explanation about what is going on here.
    </span>

    <span style="color:red">
     Why do we need to have v2 existentially quantified, for example, when p is only pointing to a single value?
    </span>

    ```
    ∀p.
    ∀v1.
    { p ↦ P }
    read(p)
    { \return. ∃P_post. (p ↦ P_post) /\ return = P /\ P = P_post }
    ```

    CN’s `take` notation is just an alternative syntax for quantification over the values of resources, but a useful one: the `take` notation syntactically restricts how these quantifiers can be used to ensure CN can always infer them.

_Exercise._ <span style="color:blue">JWS: TODO, probably double</span>

## Writing through pointers

Let’s explore resources and their outputs in another example. The C function
`incr` takes an `unsigned int` pointer `p` and increments the value in the
memory cell that it points to.

<span style="color:red">
BCP: unsigned! (there are both signed and unsigned versions at the
moment -- how do they relate?)
</span>
```c title="exercises/slf0_basic_incr.signed.c"
--8<--
exercises/slf0_basic_incr.signed.c
--8<--
```

In the precondition we assert ownership of resource `Owned<unsigned int>(p)`,
binding its output/pointee value to `P`, and use `P` to specify
that `p` must point to a sufficiently small value at the start of
the function so as not to overflow when incremented. The postcondition
asserts ownership of `p` with output `P_post`, as before, and uses
this to express that the value `p` points to is incremented by
`incr`: `P_post == P + 1i32`.

_Exercise._ Write a specification for `inplace_double`, which takes a pointer
`p` and doubles the pointee value. Make sure your postcondition captures the
function's intended behavior.

<span style="color:blue">JWS: TODO make these unsigned int</span>

```c title="exercises/slf3_basic_inplace_double.c"
--8<--
exercises/slf3_basic_inplace_double.c
--8<--
```

## No memory leaks

In the specifications we have written so far, functions that receive resources as part of their precondition also return this ownership in their postcondition.

Let’s try the `read` example from earlier again, but without such a postcondition:

```c title="exercises/read.broken.c"
--8<--
exercises/read.broken.c
--8<--
```

CN rejects this program with the following message:
```
> cn test exercises/read.broken.c
...
FAILED
...
Postcondition leak check failed, ownership leaked for pointer 0x1243d8a82
...
```
<span style="color:red">
BCP: Explain what that means.  Update if the output format changes.
</span>

<!-- CN has typechecked the function and verified (1) that it is safe to
execute under the precondition (given ownership `Owned<unsigned int>(p)`)
and (2) that the function (vacuously) satisfies its postcondition. But
following the check of the postcondition it finds that not all
resources have been "used up". -->
<!-- JWS: I propose that this paragraph is cut, seems less clear all around than the paragraph below-->

Given the above specification, `read` leaks memory: it takes ownership, does not return it, but also does not deallocate the owned memory or otherwise dispose of it. In CN this is a type error.

CN requires that every resource passed into a function has to be either
_returned_ to the caller or else _destroyed_ by deallocating the owned area of
memory (as we shall see later). CN’s motivation for this choice is its focus on
low-level systems software in which memory is managed manually; in this context,
memory leaks are typically very undesirable.
<!-- As a consequence, function specifications have to do precise bookkeeping of
their resource footprint and, in particular, return any unused resources back to
the caller. -->

_Exercise._ <span style="color:blue">JWS: TODO</span>

## Disjoint memory regions

When functions manipulate multiple pointers, we can assert ownership of each
one, just like before. But there is an additional twist: simultaneously owning
resources for two pointers implies that these pointers refer to _disjoint_
regions of memory.

<span style="color:blue">JWS: TODO five/six example</span>

_Exercise._ Write a specification for the function `transfer`, shown below.

```c title="exercises/slf8_basic_transfer.c"
--8<--
exercises/slf8_basic_transfer.c
--8<--
```

## Ownership of structured objects

So far, our examples have worked with just integers and pointers, but
larger programs typically also manipulate compound values, often
represented using C `struct`s. Specifying functions manipulating
structs works in much the same way as with basic types.

For instance, the following example uses a `struct` `point` to
represent a point in two-dimensional space. The function `transpose`
swaps a point’s `x` and `y` coordinates.

```c title="exercises/transpose.c"
--8<--
exercises/transpose.c
--8<--
```

Here the precondition asserts ownership for `p`, at type `struct
point`; the output `P_post` is a value of type `struct point`, i.e. a
record with members `x` and `y`. The postcondition similarly asserts
ownership of `p`, with output `P_post`, and asserts the coordinates
have been swapped, by referring to the members of `P` and `P_post`
individually.

The reason `Owned` needs a C-type annotation is so that it can (a)
figure out the size of the sub-heap being claimed and (b) figure out
how one may need to destructure the type (unions, struct fields and
padding, arrays). The relationship is that for `take x =
Owned<ct>(expr)` we have `expr : pointer, x : to_basetype(ct)`.

<span style="color:red">
There is a design decision to consider here rems-project/cerberus#349
</span>

_Exercise._ <span style="color:blue">JWS: TODO</span>
