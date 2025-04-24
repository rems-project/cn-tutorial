# Working with pointers

{{hidden("AZ: Added a summary paragraph.")}}
This chapter introduces how to write and test specifications for 
functions that manipulate memory through pointers. Using CN's 
resource-based model, you'll learn the concepts of memory ownership
and how to express it in CN specifications. You'll learn how to use
these concepts to address common pointer related bugs that arise due
to incorrect pointer dereferences `*p`, memory leaks and more.

So far we’ve only considered functions manipulating numeric
values. Specifications become more interesting when _pointers_ are
involved, because the safety of memory accesses via pointers has to be
taken into account in addition to the values being read or written. 

CN helps here by using the idea of _resources_ and _ownership_, drawn 
from separation logic. A _resource_, intuitively, represents the 
permission to access a region of memory. We now show how CN uses these
 ideas to prevent bugs like reading from uninitialized memory, writing
 to overlapping regions, and memory leaks.

Let’s look at a simple example. The function `read` takes a pointer 
`p` to an unsigned integer and returns the pointee value `*p` - the 
value stored at the location pointed to by a pointer.

```c title="exercises/read.c"
--8<--
exercises/read.c
--8<--
```

Running `cn test` on this example produces an error that looks like this:
```
Testing read::read:
FAILED

************************ Failed at *************************
function read, file ./read-exec.c, line 19
Load failed.
  ==> 0x12294ca70[0] (0x12294ca70) not owned
********************** Failing input ***********************

unsigned int* p = (unsigned int*)(12294ca70);
read(p);
```

The problem? CN doesn’t know about the ownership of the memory 
pointed to by `p`. It assumes nothing is safe unless proven otherwise
— a good assumption when working with pointers in C. In other words,
for the read `*p` to be safe, we need to know that the function has
permission to access the memory pointed to by `p`. We next explain
how to represent this permission.

## Read-Write(RW) Resources {{todo("AZ: RW is never expanded. I am assuming it is read-write.")}}
Given a pointer `p` to a C-type `T`, the resource `RW<T>(p)` asserts
_ownership_ of a memory region at location `p` of the size of the C type
`T`.

{{ hidden("BCP: The description of the T argument could be postponed
   for a while, if we removed `<unsigned int>` annotations everywhere.
   But I'm not convinced that this suppressing is helpful; it really
   depends whether real C code often uses pointers to things whose
   size CN can determine automatically, and I don't have a clear
   enough picture of what those are...") }}

We can ensure the safe execution of `read` by adding
a precondition that requires ownership of `RW<unsigned int>(p)`, as
shown in the below example. (The `take ... =` part will be explained shortly.) Since
reading the pointer does not disturb its value,
we can also add a corresponding postcondition, whereby `read` returns
ownership of `p` after it is finished executing, in the form of
another `RW<unsigned int>(p)` resource.

```c title="solutions/read.c"
--8<--
solutions/read.c
--8<--
```

This specification can be read as follows:

- any function calling `read` must provide a resource
  `RW<unsigned int>(p)` to pass into `read` (thus giving permission to
  read `*p`), and

- the caller will receive back a resource `RW<unsigned int>(p)` when
  `read` returns. In other words, the function will return the
  permission unchanged when finished.

## Reasoning About Pointee Values

In addition to reasoning about memory accessed by pointers, we often
want to reason about the actual values that the pointers point to.
For example, we may want to specify that a function returns the value 
pointed to by its input, or that it leaves the value unchanged.

CN let's us express this by naming the pointee value in both the
precondition and the postcondition. In the above specification of 
`read`, the `take P = ...` clause in the precondition assigns the name 
`P` to the pointee value of `p`. Once we’ve named the initial value, 
we can refer back to it in the postcondition. For instance, in the 
read function, we expect it to return the value stored at `*p`, and we 
also expect that this value hasn’t changed. We can express both of 
these expectations directly:

1. `return == P` specifies that `read` returns `P`, the initial
  pointee value of `p`, and
2. `P_post == P` specifies that the pointee values `P` and `P_post` 
  before and after execution of `read` (respectively) are the same.

We can now strengthen the specification of `read` as shown below.

```c title="exercises/read2.c"
--8<--
exercises/read2.c
--8<--
```

??? note "Aside (for separation-logic experts)"
    _Aside._ In standard separation logic, the equivalent specification for `read` could have been phrased as follows (where `\return` binds the return value in the postcondition):

    {{ todo("    Sainati: as a separation logic noob, I would love a more detailed explanation about what is going on here.
    ") }}

    {{ todo("     Why do we need to have v2 existentially quantified, for example, when p is only pointing to a single value?
    ") }}

    ```
    ∀p.
    ∀P.
    { p ↦ P }
    read(p)
    { \return. ∃P_post. (p ↦ P_post) and return = P and P = P_post }
    ```

    CN’s `take` notation is just an alternative syntax for quantification over the values of resources, but a useful one: the `take` notation syntactically restricts how these quantifiers can be used to ensure CN can always infer them.

### Exercises

_Exercise:_ Pointers, Values, and a Bit of Arithmetic  
Write a specification for `double_it`, a function which takes a 
pointer `p` and returns twice the pointee value. Running `cn test` 
on this correct implementation should succeed,
```c title="exercises/double_it.c"
--8<--
exercises/double_it.c
--8<--
```
while running `cn test` on this incorrect implementation
```C
  unsigned int n = *p;
  unsigned int m = n + n;
  *p = 0;
  return m;
```
and this incorrect implementation
```C
  unsigned int n = *p;
  unsigned int m = n + n + n;
  return m;
```
should fail.

## Writing Through Pointers

Now let’s look at a function that modifies memory. Here, we have an 
example where data is written to a pointer. The function `incr` takes 
a pointer `p` and increments the value in the memory cell that it
points to.

```c title="exercises/slf0_basic_incr.c"
--8<--
exercises/slf0_basic_incr.c
--8<--
```

In the specification:  

- `take P = RW<unsigned int>(p)` in the precondition binds the 
  initial pointee value to `P`,

-  `take P_post = RW<unsigned int>(p);` in the postcondition binds the
    pointee value _after_ function execution to `P_post`, and finally,

-  `P_post == P + 1u32` express that the value `p` points to is
    incremented by `1`.

### Exercises

_Exercise:_ Specifying a Function that Modifies Memory In-Place  
Write a specification for `inplace_double`, which takes a pointer
`p` and doubles the pointee value. Make sure your postcondition captures the
function's intended behavior.

```c title="exercises/slf3_basic_inplace_double.c"
--8<--
exercises/slf3_basic_inplace_double.c
--8<--
```

## What Happens If Ownership Isn’t Returned? Understanding Memory Leaks

In the specifications we have written so far, functions that receive resources as part of their precondition also return this ownership in their postcondition.

Let’s try the `read` example from earlier again, but without such a postcondition:

```c title="exercises/read.broken.c"
--8<--
exercises/read.broken.c
--8<--
```

CN rejects this program with the following message:
```
Testing read::read:
FAILED

************************ Failed at *************************
function read, file ./read.broken-exec.c, line 26
Postcondition leak check failed, ownership leaked for pointer 0x1201e8a78

********************** Failing input ***********************

void* p0 = malloc(4);
*((unsigned int*)p0) = 17;
unsigned int* p = (unsigned int*)(p0);
read(p);
```

The `cn test` error report tells us that the `function read` failed 
the postcondition leak check and `ownership leaked` for a pointer. It 
also provides a failing input — i.e., a snippet of C code that will 
construct a heap state on which the test fails.

So, what went wrong? CN found that the function `read` leaks memory: 
it takes ownership of `p`, but does not return it or deallocate the 
memory.

In CN, **every resource must be accounted for**: every resource passed
into a function has to be either _returned_ to the caller or else 
_destroyed_ by explicitly deallocating the RW area of memory (as we 
shall see later).

CN’s motivation for this choice is its focus on low-level systems software in
which memory is managed manually; in this context, memory leaks are typically
very undesirable. As a consequence, function specifications have to do precise
bookkeeping of their resource footprint and, in particular, return any unused
resources back to the caller.

## Disjoint Memory Regions

When functions manipulate multiple pointers, we can assert ownership of each
one, just like before. But there is an additional twist: simultaneously owning
resources for two pointers implies that these pointers refer to _disjoint_
regions of memory.

Consider this example to see when disjointedness matters:

```c title="exercises/five_six.c"
--8<--
exercises/five_six.c
--8<--
```

The postcondition claims that the function returns `5`. Observe that this is
only true when `p` and `q` are disjoint; otherwise, the write to `q` would
override the write to `p`. In CN, we can make this assumption for free — no
extra work is needed to assert that the pointers are disjoint.

### Exercises

_Exercise:_ Write a specification for the function `transfer`, shown below.

```c title="exercises/slf8_basic_transfer.c"
--8<--
exercises/slf8_basic_transfer.c
--8<--
```

## Ownership of Structured Objects

So far, we've focused on functions that operate on simple types like
integers and pointers. But real-world C programs often manipulate 
compound data types, such as _structs_. CN supports reasoning about 
C _structs_ in a way that extends naturally from what we’ve already 
seen. 

Specifying functions manipulating _structs_ works in much the 
same way as with basic types. Just as we can take ownership of a 
single unsigned int value via `RW<unsigned int>(p)`, we can also take 
ownership of an entire struct using its type - `RW<struct point>(p)`.

In the following example, we show how to write CN specifications about
a `struct point` that is used to represent a point in two-dimensional 
space. Consider the function `transpose`, which swaps a point’s 
`x` and `y` coordinates.

```c title="exercises/transpose.c"
--8<--
exercises/transpose.c
--8<--
```

In the precondition, we use `take P = RW<struct point>(p)` to require 
ownership of the entire memory region pointed to by `p`, and bind the 
contents of the region to `P`. Accordingly in the postcondition, `P` 
and `P_post` are values with type `struct point`, i.e., they are 
records with members `x` and `y`. The postcondition specifies the 
return of ownership using `take P_post = RW<struct point>(p)`. 
Furthermore, it specifies the intended effect of the function: that 
the `x` and `y` fields have been swapped.

{{ later("It would be nice to add an exercise that involves
using the error messages to find a bug.") }}
