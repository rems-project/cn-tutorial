# Pointers and Simple Ownership

<span style="color:red">
Things to do:
</span>

    - read.c
        - unannotated version fails tests
             - need to explain how to figure out WHY testing fails!
        - explain ownership (copy/move from verification tutorial)
        - version with proper spec works better!
        - (lots of useful text)
        - read.broken.c demonstrates linearity of resource usage
    - exercises:
        - quadruple_mem
        - abs_mem (doesn't work, but we can use the other examples
          from the previous section)
    - slf0_basic_incr_signed.c
        shows the difference between Block and Owned
    - exercises
        - zero.c
        - basic_inplace_double.c involves UB, so skip?
        - maybe something about swapping pointers?

    - add_read  (but changing it to swapping or something, to avoid UB
      issues)

    - everything up through pointers to compound objects seems to work
      well, except for some of the resource inference stuff

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

Running CN on this example produces the following error:

```
cn test read.c
Compiled 'read_test.c'.
Compiled 'read-exec.c'.
Compiled 'cn.c'.

Linked C *.o files.

Using seed: 65a9c0d1f79889a9
Testing read::read:
FAILED

Testing Summary:
cases: 1, passed: 0, failed: 1, errored: 0, skipped: 0
```

For the read `*p` to be safe, we need to know that the function has
permission to access the memory pointed to by `p`.  This permission is
represented by a _resource_ `Owned<unsigned int>(p)`.
<span style="color:red">
BCP: Is that right?? Should it be just Owned<unsigned int>(p)? Or just
Owned(p)?? (I think just Owned(p) is OK, and we should use that
everywhere it's OK!  We'll need a bit of explanation when we reach the
first place where it is _not_ OK.)
</span>

## Owned resources

Given a C-type `T` and pointer `p`, the resource `Owned<T>(p)` asserts
_ownership_ of a memory region at location `p` of the size of the C type
`T`.  If `T` is a single-word type, then `<T>` can be omitted.
<!-- TODO: BCP: Do we mean 32-bit word here?? -->
<!-- TODO: BCP: Maybe the T argument can be postponed for a while...? -->

In this example, we can ensure the safe execution of `read` by adding
a precondition that requires ownership of `Owned<unsigned int>(p)`, as
shown below. (For now ignore the `take ... =` part.) Since reading the pointer does not disturb its value,
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

<span style="color:red">
BCP: Is this going slowly enough for "real-world
engineers"? Where do we need more detail? 
</span>

## Resource outputs

<span style="color:red"> BCP: The idea that "resources have outputs"
is very mind-boggling to many new users, _especially_ folks with some
separation logic background. Needs to be explained very
carefully. Also, there's some semantic muddle in the terminology: Is a
resource (1) a thing in the heap, (2) a thing in the heap that one is
currently holding, or (3) the act of holding a thing in the heap?
These are definitely not at all the same thing, but our language at
different points suggests all three! To me, (1) is the natural sense
of the word "resource"; (2) is somewhat awkward, and (3) is extremely
awkward.  </span>

A caller of `read` may also wish to know that `read` actually returns
the correct value (i.e., the thing that `p` points to), and also that
it does not change memory at location `p`. To phrase both we need a
way to refer to the pointee of `p`.

In CN, resources have _outputs_. Each resource outputs the information
that can be derived from ownership of the resource. What information
is returned is specific to the type of resource. A resource
`Owned<T>(p)` (for some C-type `T`) outputs the _pointee value_ of
`p`, since that can be derived from the resource ownership: assume you
have a pointer `p` and the associated ownership, then this uniquely
determines the pointee value of `p`.

<span style="color:red">
BCP: ... in a given heap! (The real problem here is that "and the associated ownership" is pretty vague.) 
</span>
<span style="color:red">
Dhruv: Perhaps mentioning sub-heaps will help? 
</span>

CN uses the `take` notation seen in the example above to bind the
output of a resource to a new name. The precondition `take P =
Owned<unsigned int>(p)` does two things: (1) it assert ownership of resource
`Owned<unsigned int>(p)`, and (2) it binds the name `P` to the resource output,
here the pointee value of `p` at the start of the function. Similarly,
the postcondition introduces the name `P_post` for the pointee value
on function return.

<span style="color:red">
BCP: But, as we've discussed, the word "take" in the postcondition is
quite confusing: What it's doing is precisely the _opposite_ of
"taking" the resournce, not taking it but giving it back!! It would be
much better if we could choose a more neutral word that doesn't imply
either taking or giving. E.g. "resource".  (I forget if we decided on
something like this in the last round of syntax changes...)
</span>

<span style="color:red">
BCP: This might be a good place for a comment on naming
conventions. Plus a pointer to a longer discussion if needed.  
</span>

That means we can use the resource outputs from the pre- and postcondition to strengthen the specification of `read` as planned. We add two new postconditions specifying

1. that `read` returns `P` (the initial pointee value of `p`), and
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

## Linear resource ownership

In the specifications we have written so far, functions that receive resources as part of their precondition also return this ownership in their postcondition.

Let’s try the `read` example from earlier again, but with a postcondition that does not return the ownership:

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

CN has typechecked the function and verified (1) that it is safe to
execute under the precondition (given ownership `Owned<unsigned int>(p)`)
and (2) that the function (vacuously) satisfies its postcondition. But
following the check of the postcondition it finds that not all
resources have been "used up".

Indeed, given the above specification, `read` leaks memory: it takes ownership, does not return it, but also does not deallocate the owned memory or otherwise dispose of it. In CN this is a type error.

CN’s resources are _linear_. This means not only that resources cannot be duplicated, but also that resources cannot simply be dropped or "forgotten". Every resource passed into a function has to be either _returned_ to the caller or else _destroyed_ by deallocating the owned area of memory (as we shall see later).

CN’s motivation for linear tracking of resources is its focus on
low-level systems software in which memory is managed manually; in
this context, memory leaks are typically very undesirable. As a
consequence, function specifications have to do precise bookkeeping of
their resource footprint and, in particular, return any unused
resources back to the caller.

## Exercises

_Quadruple_. Specify the function `quadruple_mem`, which is similar to
the earlier `quadruple` function, except that the input is passed as a
pointer to an `unsigned int`. Write a specification that takes ownership
of this pointer on entry and returns this ownership on exit, leaving
the pointee value unchanged.

```c title="exercises/slf_quadruple_mem.c"
--8<--
exercises/slf_quadruple_mem.c
--8<--
```

_Abs_. Give a specification to the function `abs_mem`, which computes
the absolute value of a number passed as an `int` pointer.
XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX Fix

```c title="exercises/abs_mem.c"
--8<--
exercises/abs_mem.c
--8<--
```

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

## Writing through pointers

Let’s explore resources and their outputs in another example. The C function `incr` takes an `unsigned int` pointer `p` and increments the value in the memory cell that it poinbts to.

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

If we incorrectly tweaked this specification and used `Block<unsigned int>(p)` instead of `Owned<unsigned int>(p)` in the precondition, as below, then CN would reject the program.

<span style="color:red">
BCP: change it to unsigned...
</span>


```c title="exercises/slf0_basic_incr.signed.broken.c"
--8<--
exercises/slf0_basic_incr.signed.broken.c
--8<--
```

CN reports:
<span style="color:red">
BCP: fix it...
</span>

```
build/solutions/slf0_basic_incr.signed.broken.c:6:11: error: Missing resource for reading
int n = \*p;
^~
Resource needed: Owned<signed int>(p)
Consider the state in /var/folders/\_v/ndl32wpj4bb3y9dg11rvc8ph0000gn/T/state_5da0f3.html
```

## Exercises

_Zero._ Write a specification for the function `zero`, which takes a pointer to _uninitialised_ memory and initialises it to `0`.

```c title="exercises/zero.c"
--8<--
exercises/zero.c
--8<--
```

_In-place double._ Give a specification for the function `inplace_double`, which takes an `unsigned int` pointer `p` and doubles the pointee value: specify the precondition needed to guarantee safe execution and a postcondition that captures the function’s behaviour.

```c title="exercises/slf3_basic_inplace_double.c"
--8<--
exercises/slf3_basic_inplace_double.c
--8<--
```

## Multiple owned pointers

When functions manipulate multiple pointers, we can assert 
ownership of each one, just like before. But there is an additional
twist: pointer ownership in CN is _unique_ -- that is, simultaneously owning
resources for two pointers implies that these
pointers refer to _disjoint_ regions of memory.

The following example shows the use of two `Owned` resources for
accessing two different pointers by a function `add`, which reads
two `unsigned int` values in memory, at locations `p` and `q`, and
returns their sum.

<span style="color:red">
BCP: The way I've been naming things is not working that well
here. The problem is that in examples like this we compute "thing
pointed to by p" at both C and CN levels. At the C level, the thing
pointed to by p obviously cannot also be called p, so it doesn't make
sense for it to be called P at the CN level, right?
</span>

```c title="exercises/add_read.c"
--8<--
exercises/add_read.c
--8<--
```

<span style="color:red">
BCP: Does this belong here?  Could it go in the later section on numeric types?
</span>
The CN variables `P` and `Q` (resp. `P_post` and `Q_post`) for the pointee values of `p` and `q` before (resp. after) the execution of `add` have CN basetype `u32`, so unsigned 32-bit integers, matching the C `unsigned int` type. Like C’s unsigned integer arithmetic, CN unsigned int values wrap around when exceeding the value range of the type.
Hence, the postcondition `return == P + Q` holds also when the sum of `P` and `Q` is greater than the maximal `unsigned int` value.

## Exercises

_Swap._ Specify the function `swap`, which takes two owned `unsigned int` pointers and swaps their values.

```c title="exercises/swap.c"
--8<--
exercises/swap.c
--8<--
```

_Transfer._ Write a specification for the function `transfer`, shown below.

```c title="exercises/slf8_basic_transfer.c"
--8<--
exercises/slf8_basic_transfer.c
--8<--
```
