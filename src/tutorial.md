include(src/setup.m4)




---
title: CN tutorial
fontsize: 18px
mainfont: sans-serif
linestretch: 1.4
maxwidth: 45em
lang: en-GB
toc-title: Table of contents
header-includes: |
  <style>
  body { max-width: 650px }
  h1, h2, h3, h4, h5 { color: hsl(219, 50%, 50%); }
  body > .sourceCode {
    padding: 5px;
    border-radius: 5px;
    border: 1px solid hsl(44, 7%, 80%);
    background-color: hsl(44, 7%, 96%);
  }
  </style>
---


CN is a type system for verifying C code, focusing especially on low-level systems code. Compared to the normal C type system, CN checks not only that expressions and statements follow the correct typing discipline for C-types, but also that the C code executes *safely* --- does not raise C undefined behaviour --- and *correctly* --- according to strong user-defined specifications. To accurately handle the complex semantics of C, CN builds on the [Cerberus semantics for C](https://github.com/rems-project/cerberus/).

This tutorial introduces CN along a series of examples, starting with basic usage of CN on simple arithmetic functions and slowly moving towards more elaborate separation logic specifications of data structures.

Many examples are taken from Arthur Charguéraud's excellent [Separation Logic Foundations](https://softwarefoundations.cis.upenn.edu). These example have names starting with "slf...".

## Installation


To fetch and install CN, check the Cerberus repository at <https://github.com/rems-project/cerberus> and follow the instructions in [`backend/cn/INSTALL.md`](https://github.com/rems-project/cerberus/blob/master/backend/cn/INSTALL.md).

Once completed, type `cn --help` in your terminal to ensure CN is installed and found by your system. This should print the list of available options CN can be executed with.

To apply CN to a C file, run `cn CFILE`.




## Basic usage

### First example

For a first example, let's look at a simple arithmetic function: `add`, shown below, takes two `int` arguments, `x` and `y`, and returns their sum.

include_example(exercises/0.c)

Running CN on the example produces an error message:
```
cn exercises/0.c
[1/1]: add
exercises/0.c:3:10: error: Undefined behaviour
  return x+y;
         ~^~
an exceptional condition occurs during the evaluation of an expression (§6.5#5)
Consider the state in /var/folders/_v/ndl32wpj4bb3y9dg11rvc8ph0000gn/T/state_393431.html
```

CN rejects the program because it has *C undefined behaviour*, meaning it is not safe to execute. CN points to the relevant source location, the addition `x+y`, and paragraph §6.5#5 of the C language standard that specifies the undefined behaviour. It also puts a link to an HTML file with more details on the error to help in diagnosing the problem.

Inspecting this HTML report (as we do in a moment) gives us possible example values for `x` and `y` that cause the undefined behaviour and hint at the problem: for very large values for `x` and `y`, such as $1073741825$ and $1073741824$, the sum of `x` and `y` can exceed the representable range of a C `int` value: $1073741825 + 1073741824 = 2^31+1$, so their sum is larger than the maximal `int` value, $2^31-1$.

Here `x` and `y` are *signed integers*, and in C, signed integer *overflow* is undefined behaviour (UB). Hence, `add` is only safe to execute for smaller values. Similarly, *large negative* values of `x` and `y` can cause signed integer *underflow*, also UB in C. We therefore need to rule out too large values for `x` and `y`, both positive and negative, which we do by writing a CN function specification.


### First function specification

Shown below is our first function specification, for `add`, with a precondition that constraints `x` and `y` such that the sum of `x` and `y` lies between $-2147483648$ and $2147483647$, so within the representable range of a C `int` value.

include_example(solutions/0.c)

In detail:

- Function specification are given using special `/*@ ... @*/` comments, placed in-between the function argument list and the function body.

- The keyword `requires` starts the pre-condition, a list of one or more CN conditions separated by semicolons.

- In function specifications, the names of the function arguments, here `x` and `y`, refer to their *initial values*. (Function arguments are mutable in C.)

- `let sum = (i64) x + (i64) y` is a let-binding, which defines `sum` as the value `(i64) x + (i64) y` in the remainder of the function specification.

- Instead of C syntax, CN uses Rust-like syntax for integer types, such as `u32` for 32-bit unsigned integers and `i64` for signed 64-bit integers to make their sizes unambiguous. Here, `x` and `y`, of C-type `int`, have CN type `i32`.

- To define `sum` we cast `x` and `y` to the larger `i64` type, using syntax `(i64)`, which is large enough to hold the sum of any two `i32` values.

- Finally, we require this sum to be in-between the minimal and maximal `int` value. Integer constants, such as `-2147483648i64`, must specifiy their CN type (`i64`).

Running CN on the annotated program passes without errors. This means with our specified precondition, `add` is safe to execute.

We may, however, wish to be more precise. So far the specification gives no information to callers of `add` about its output. To also specify the return values we add a postcondition, using the `ensures` keyword.

include_example(solutions/1.c)

Here we use the keyword `return`, only available in function postconditions, to refer to the return value, and equate it to `sum` as defined in the preconditions, cast back to `i32` type: `add` returns the sum of `x` and `y`.



Running CN confirms that this postcondition also holds.


### Error reports

In the original example CN reported a type error due to C undefined behaviour. While that example was perhaps simple enough to guess the problem and solution, this can become quite challenging as program and specification complexity increases. Diagnosing type errors is therefore an important part of using CN. CN tries to help with that by producting detailed error information, in the form of an HTML error report.

Let's return to the type error from earlier (`add` without precondition) and take a closer look at this report. The report comprises two sections.

![**CN error report**](src/images/0.error.png)

**Path.** The first section, "Path to error", contains information about the  control-flow path leading to the error.

When type checking a C function, CN checks each possible control-flow path through the program individually. If CN detects UB or a violation of user-defined specifications, CN reports the problematic control-flow path, as a nested structure of statements: paths are split into sections, which group together statements between high-level control-flow positions (e.g. function entry, the start of a loop, the invocation of a `continue`, `break`, or `return` statement, etc.); within each section, statements are listed by source code location; finally, per statement, CN lists the typechecked sub-expressions, and the memory accesses and function calls within these.

In our example, there is only one possible control-flow path: entering the function body (section "function body") and executing the block from lines 2 to 4, followed by the return statement at line 3. The entry for the latter contains the sequence of sub-expressions in the return statement, including reads of the variables `x` and `y`.

In C, local variables in a function, including its arguments, are mutable and their address can be taken and passed as a value. CN therefore represents local variables as memory allocations that are manipulated using memory reads and writes. Here, type checking the return statement includes checking memory reads for `x` and `y`, at their locations `&ARG0` and `&ARG1`. The path report lists these reads and their return values: the read at `&ARG0` returns `x` (that is, the value of `x` originally passed to `add`); the read at `&ARG1` returns `y`. Alongside this symbolic information, CN displays concrete values:

- `1073741825i32 /* 0x40000001 */` for x (the first value is the decimal representation, the second, in `/*...*/` comments, the hex equivalent) and

- `1073741824i32 /* 0x40000000 */` for `y`.

For now, ignore the pointer values `{@0; 4}` for `x` and `{@0; 0}` for `y`.

These concrete values are part of a *counterexample*: a concrete valuation of variables and pointers in the program that that leads to the error. (The exact values may vary on your machine, depending on the version of Z3 installed on your system.)


**Proof context.** The second section, below the error trace, lists the proof context CN has reached along this control-flow path.

"Available resources" lists the owned resources, as discussed in later sections.

"Variables" lists counterexample values for program variables and pointers. In addition to `x` and `y`, assigned the same values as above, this includes values for their memory locations `&ARG0` and `&ARG1`, function pointers in scope, and the `__cn_alloc_history`, all of which we ignore for now.

Finally, "Constraints" records all logical facts CN has learned along the path. This includes user-specified assumptions from preconditions or loop invariants, value ranges inferred from the C-types of variables, and facts learned during the type checking of the statements. Here (`add` without precondition) the only constraints are some contraints inferred from C-types in the code.

- For instance, `good<signed int>(x)` says that the initial value of `x` is a "good" `signed int` value (i.e. in range). Here `signed int` is the same type as `int`, CN just makes the sign explicit. For integer types `T`, `good<T>` requires the value to be in range of type `T`; for pointer types `T` it also requires the pointer to be aligned. For structs and arrays this extends in the obvious way to struct members or array cells.

- `repr<T>` requires representability (not alignment) at type `T`, so `repr<signed int*>(&ARGO)`, for instance, records that the pointer to `x` is representable at C-type `signed int*`;

- `aligned(&ARGO, 4u64)`, moreover, states that it is 4-byte aligned.




### Another arithmetic example

Let's apply what we know so far to another simple arithmetic example.

The function `doubled`, shown below, takes an int `n`, defines `a` as `n` incremented, `b` as `n` decremented, and returns the sum of the two.

include_example(exercises/slf1_basic_example_let.signed.c)

We would like to verify this is safe, and that `doubled` returns twice the value of `n`. Running CN on `doubled` leads to a type error: the increment of `a` has undefined behaviour.

As in the first example, we need to ensure that `n+1` does not overflow and `n-1` does not underflow. Similarly also `a+b` has to be representable at `int` type.

include_example(solutions/slf1_basic_example_let.signed.c)

We can specify these using a similar style of precondition as in the first example. We first define `n_` as `n` cast to type `i64` --- i.e. a type large enough to hold `n+1`, `n-1` and `a+b` for any possible `i32` value for `n`. Then we specify that decrementing `n_` does not go below the minimal `int` value, that incrementing `n_` does not go above the maximal value, and that `n` doubled is also in range. These preconditions together guarantee safe execution.

To capture the functional behaviour, the postcondition specifies that `return` is twice the value of `n`.

### Exercise

**Quadruple.** Specify the precondition needed to ensure safety of the C function `quadruple`, and a postcondition that describes its return value.

include_example(exercises/slf2_basic_quadruple.signed.c)

**Abs.** Give a specification to the C function `abs`, which computes the absolute value of a given `int` value. To describe the return value, use CN's ternary "`_ ? _ : _`" operator. Given a boolean `b`, and expressions `e1` and `e2` of the same basetype, `b ? e1 : e2` returns `e1` if `b` holds and `e2` otherwise.

include_example(exercises/abs.c)

## Pointers and simple ownership

So far we've only considered example functions manipulating integer values. Verification becomes more interesting and challenging when *pointers* are involved, because the safety of memory accesses via pointers has to be verified.

CN uses *separation logic resource types* and the concept of *ownership* to reason about memory accesses. A resource is the permission to access a region of memory. Unlike logical constraints, resource ownership is *unique*, meaning resources cannot be duplicated.

Let's look at a simple example. The function `read` takes an `int` pointer `p` and returns the pointee value.

include_example(exercises/read.c)

Running CN on this example produces the following error:
```
cn exercises/read.c
[1/1]: read
exercises/read.c:3:10: error: Missing resource for reading
  return *p;
         ^~
Resource needed: Owned<signed int>(p)
Consider the state in /var/folders/_v/ndl32wpj4bb3y9dg11rvc8ph0000gn/T/state_403624.html
```

For the read `*p` to be safe, ownership of a resource is missing: a resource `Owned<signed int>(p)`.

### The Owned resource type

Given a C-type `T` and pointer `p`, the resource `Owned<T>(p)` asserts ownership of a memory cell at location `p` of the size of C-type `T`. It is is CN's equivalent of a points-to assertion in separation logic (indexed by C-types `T`).

In this example we can ensure the safe execution of `read` by adding a precondition that requires ownership of `Owned<int>(p)`, as shown below. For now ignore the notation `take ... = Owned<int>(p)`. Since `read` maintains this ownership, we also add a corresponding post-condition, whereby `read` returns ownership of `p` after it is finished executing, in the form of another `Owned<int>(p)` resource.

include_example(solutions/read.c)

This specifications means that

- any function calling `read` has to be able to provide a resource `Owned<int>(p)` to pass into `read`, and

- the caller will receive back a resource `Owned<int>(p)` when `read` returns.

### Resource outputs

However, a caller of `read` may also wish to know that `read` actually returns the correct value, the pointee of `p`, and also that it does not change memory at location `p`. To phrase both we need a way to refer to the pointee of `p`.

In CN resources have *outputs*. Each resource outputs the information that can be derived from ownership of the resource. What information is returned is specific to the type of resource. A resource `Owned<T>(p)` (for some C-type `T`) outputs the *pointee value* of `p`, since that can be derived from the resource ownership: assume you have a pointer `p` and the associated ownership, then this uniquely determines the pointee value of `p`.

CN uses the `take`-notation seen in the example above to refer to the output of a resource, introducing a new name binding for the output. The precondition `take v1 = Owned<int>(p)` from the precondition does two things: (1) it assert ownership of resource `Owned<int>(p)`, and (2) it binds the name `v1` to the resource output, here the pointee value of `p` at the start of the function. Similarly, the postcondition introduces the name `v2` for the pointee value on function return.

That means we can use the resource outputs from the pre- and postcondition to strengthen the specification of `read` as planned. We add two new postconditions: we specify

#. that `read` returns `v1` (the initial pointee value of `p`), and

#. that the pointee values `v1` and `v2` before and after execution of `read` (respectively) are the same.

include_example(solutions/read2.c)


**Aside.** In standard separation logic the equivalent specification for `read` could have been phrased as follows (where `return` binds the return value in the postcondition):
```
∀p.
∀v1. { p ↦ v1 }
     read(p)
     { return. ∃v2. (p ↦ v2) /\ return = v1 /\ v1 = v2 }
```
CN's `take` notation is just alternative syntax for quantification over the values of resources, but a useful one: the `take` notation syntactically restricts how these quantifiers can be used to ensure CN can always infer them.


### Exercises

**Quadruple**. Specify the function `quadruple_mem`, that is similar to the earlier `quadruple` function, except that the input is passed as an `int` pointer. Write a specification that takes ownership of this pointer on entry and returns this ownership on exit, leaving the pointee value unchanged.

include_example(exercises/slf_quadruple_mem.c)

**Abs**. Give a specification to the function `abs_mem`, which computes the absolute value of a number passed as an `int` pointer.

include_example(exercises/abs_mem.c)


### Linear resource ownership

In the specifications we have written so far, functions that receive resources as part of their precondition also return this ownership in their postcondition.

Let's try the `read` example from earlier again, but with a postcondition that does not return the ownership:

include_example(exercises/read.broken.c)

CN rejects this program with the following message:
```
cn build/exercises/read.broken.c
[1/1]: read
build/exercises/read.broken.c:4:3: error: Left-over unused resource 'Owned<signed int>(p)(v1)'
  return *p;
  ^~~~~~~~~~
Consider the state in /var/folders/_v/ndl32wpj4bb3y9dg11rvc8ph0000gn/T/state_17eb4a.html
```

CN has typechecked the function, verified that it is safe to execute under the precondition (given ownership `Owned<int>(p)`), and that the function (vacuously) satisfies its postcondition. But, following the check of the postcondition it finds that not all resources have been "used up".

Given the above specification, `read` leaks memory: it takes ownership, does not return it, but also does not deallocate the owned memory or otherwise dispose of it. In CN this is a type error.

CN's resource types are *linear* (as opposed to affine). This means not only that resources cannot be duplicated, but also that resources cannot simply be dropped or "forgotten". Every resource passed into a function has to either be used up by it, by returning it or passing it to another function that consumes it, or destroyed, by deallocating the owned area of memory (as we shall see later).

CN's motivation for linear tracking of resources is its focus on low-level systems software. CN checks C programs, in which, unlike higher-level garbage-collected languages, memory is managed manually, and memory leaks are typically very undesirable.

As a consequence, function specifications have to do precise "book-keeping" of their resource footprint, and, in particular, return any unused resources back to the caller.



### The Block resource type

Aside from the `Owned` resource seen so far, CN has another built-in resource type: `Block`. Given a C-type `T` and pointer `p`, `Block<T>(p)` asserts the same ownership as `Owned<T>(p)` --- so ownership of a memory cell at `p` the size of type `T` --- but in contrast to `Owned`, `Block` memory is not necessarily initialised.

CN uses this distinction to prevent reads from uninitialised memory:

- A read at C-type `T` and pointer `p` requires a resource `Owned<T>(p)`, i.e., ownership of *initialised* memory at the right C-type. The load returns the `Owned` resource unchanged.

- A write at C-type `T` and pointer `p` needs only a `Block<T>(p)` (so, unlike reads, writes to uninitialised memory are fine). The write consumes ownership of the `Block` resource (it destroys it) and returns a new resource `Owned<T>(p)` with the value written as the output. This means the resource returned from a write records the fact that this memory cell is now initialised and can be read from.

Since `Owned` carries the same ownership as `Block`, just with the additional information that the `Owned` memory is initalised, a resource `Owned<T>(p)` is "at least as good" as `Block<T>(p)` --- an `Owned<T>(p)` resource can be used whenever `Block<T>(p)` is needed. For instance CN's type checking of a write to `p` requires a `Block<T>(p)`, but if an `Owned<T>(p)` resource is what is available, this can be used just the same. This allows an already-initialised memory cell to be over-written again.

Unlike `Owned`, whose output is the pointee value, `Block` has no meaningful output: its output is `void`/`unit`.


### Write example

Let's explore resources and their outputs in another example. The C function `incr` takes an `int` pointer `p` and increments the pointee value.

include_example(solutions/slf0_basic_incr.signed.c)

In the precondition we assert ownership of resource `Owned<int>(p)`, binding its output/pointee value to `v1`, and use `v1` to specify that `p` must point to a sufficiently small value at the start of the function not to overflow when incremented. The postcondition asserts ownership of `p` with output `v2`, as before, and uses this to express that the value `p` points to is incremented by `incr`: `v2 == v1+1i32`.


If we incorrectly tweaked this specification and used `Block<int>(p)` instead of `Owned<int>(p)` in the precondition, as below, then CN would reject the program.

include_example(exercises/slf0_basic_incr.signed.broken.c)

CN reports:
```
build/solutions/slf0_basic_incr.signed.broken.c:6:11: error: Missing resource for reading
  int n = *p;
          ^~
Resource needed: Owned<signed int>(p)
Consider the state in /var/folders/_v/ndl32wpj4bb3y9dg11rvc8ph0000gn/T/state_5da0f3.html
```

The `Owned<int>(p)` resource required for reading is missing, since, as per precondition, only `Block<int>(p)` is available. Checking the linked HTML file confirms this. Here the section "Available resources" lists all resource ownership at the point of the failure:

- `Block<signed int>(p)(u)`, so ownership of uninitialised memory at location `p`; the output is a `void`/`unit` value `u` (specified in the second pair of parentheses)

- `Owned<signed int*>(&ARG0)(p)`, the ownership of (initialised) memory at location `&ARG0`, so the memory location where the first function argument is stored; its output is the pointer `p` (not to be confused with the pointee of `p`); and finally

- `__CN_Alloc(&ARG0)(void)` is a resource that records allocation information for location `&ARG0`; this is related to CN's memory-object semantics, which we ignore for the moment.


### Exercises

**Zero.** Write a specification for the function `zero`, which takes a pointer to *uninitialised* memory and initialises it to $0$.

include_example(exercises/zero.c)

**In-place double.** Give a specification for the function `inplace_double`, which takes an `int` pointer `p` and doubles the pointee value: specify the precondition needed to guarantee safe execution and a postcondition that captures the function's behaviour.

include_example(exercises/slf3_basic_inplace_double.c)


### Multiple owned pointers

When functions manipulate multiple pointers, we can assert their ownership just like before. However (as in standard separation logic) pointer ownership is unique, so simultaneous ownership of `Owned` or `Block` resources for two pointers requires these pointers to be disjoint.

The following example shows the use of two `Owned` resources for accessing two different pointers: function `add` reads two `int` values in memory, at locations `p` and `q`, and returns their sum.

include_example(exercises/add_read.c)

This time we use C's `unsigned int` type. In C, over- and underflow of unsigned integers is not undefined behaviour, so we do not need any special preconditions to rule this out. Instead, when an arithmetic operation at unsigned type goes outside the representable range, the value "wraps around".

The CN variables `m` and `n` (resp. `m2` and `n2`) for the pointee values of `p` and `q` before (resp. after) the execution of `add` have CN basetype `u32`, so unsigned 32-bit integers, matching the C `unsigned int` type. Like C's unsigned integer arithmetic, CN unsigned int values wrap around when exceeding the value range of the type.

Hence, the postcondition `return == m+n` holds also when the sum of `m` and `n` is greater than the maximal `unsigned int` value.

In the following we will sometimes use unsigned integer types to focus on specifying memory ownership, rather than the conditions necessary to show absence of C arithmetic undefined behaviour.


### Exercises

**Swap.** Specify the function `swap`, which takes two owned `unsigned int` pointers and swaps their values.

include_example(exercises/swap.c)

**Transfer.** Write a specification for the function `transfer`, shown below.

include_example(exercises/slf8_basic_transfer.c)



## Ownership of compound objects

So far all examples have worked with just integers and pointers, but larger programs typically also manipulate compound values, often represented using C struct types. Specifying functions manipulating structs works in much the same way as with basic types.

For instance, the following example uses a `struct` `point` to represent a point in two-dimensional space. The function `transpose` swaps a point's `x` and `y` coordinates.

include_example(exercises/transpose.c)

Here the precondition asserts ownership for `p`, at type `struct point`; the output `s` is a value of CN type `struct point`, i.e. a record with members `i32` `x` and `i32` `y`. The postcondition similarly asserts ownership of `p`, with output `s2`, and asserts the coordinates have been swapped, by referring to the members of `s` and `s2` individually.

**Note.** In CN, as in C, structurally equal struct types with *different tags* are not the same type.



### Compound Owned and Block resources

While one might like to think of a struct as a single (compound) object that is manipulated as a whole, C permits more flexible struct manipulation: given a struct pointer, programmers can construct pointers to *individual struct members* and pass these as values, even to other functions.

CN therefore cannot treat resources for compound C types, such as structs, as primitive, indivisible units. Instead, `Owned<T>` and `Block<T>` are defined inductively in the structure of the C-type `T`.

For struct types `T`, the `Owned<T>` resource is defined as the collection of `Owned` resources for its members (as well as `Block` resources for any padding bytes in-between). The resource `Block<T>`, similarly, is made up of `Block` resources for all members (and padding bytes).

To handle code that manipulates pointers into parts of a struct object, CN can automatically decompose a struct resource into the member resources, and recompose it, as needed. The following example illustrates this.

Recall the function `zero` from our earlier exercise. It takes an `int` pointer to uninitialised memory, with `Block<int>` ownership, and initialises the value to zero, returning an `Owned<int>` resource with output $0$.

Now consider the function `init_point`, shown below, which takes a pointer `p` to a `struct point` and zero-initialises its members by calling `zero` twice, once with a pointer to struct member `x`, and once with a pointer to `y`.

include_example(exercises/init_point.c)

As stated in its precondition, `init_point` receives ownership `Block<struct point>(p)`. The `zero` function, however, works on `int` pointers and requires `Block<int>` ownership.

CN can prove the calls to `zero` with `&p->x` and `&p->y`are safe because it decomposes the `Block<struct point>(p)` into two `Block<int>`, one for member `x`, one for member `y`. Later, the reverse happens: following the two calls to `zero`, as per `zero`'s precondition, `init_point` has ownership of two adjacent `Owned<int>` resources -- ownership for the two struct member pointers, with the member now initialised. Since the postcondition of `init_point` requires ownership `Owned<struct point>(p)`, CN combines these back into a compound resource. The resulting `Owned<point struct>` resource has for an output the struct value `s2` that is composed of the zeroed member values for `x` and `y`.

### Resource inference

To handle the required resource inference, CN "eagerly" decomposes all `struct` resources into resources for the struct members, and "lazily" re-composes them as needed.

We can see this if, for instance, we experimentally change the `transpose` example from above to force a type error. Let's insert an `/*@ assert(false) @*/` CN assertion in the middle of the `transpose` function (more on CN assertions later), so we can inspect CN's proof context shown in the error report.

include_example(exercises/transpose.broken.c)

The precondition of `transpose` asserts ownership of an `Owned<struct point>(p)` resource. The error report now instead lists under "Available resources" two resources:

- `Owned<signed int>(member_shift<point>(p, x))` with output `s.x` and

- `Owned<signed int>(member_shift<point>(p, y))` with output `s.y`

Here `member_shift<s>(p,m)` is the CN expression that constructs, from a `struct s` pointer `p`, the "shifted" pointer for its member `m`.

When the function returns the two member resources are recombined "on demand" to satisfy the postcondition `Owned<struct point>(p)`.



### Exercises

**Init point.** Insert CN `assert(false)` statements in different statement positions of `init_point` and check how the available resources evolve.

**Transpose (again).** Recreate the transpose function from before, now using the swap function verified earlier (for `struct upoint`, with unsigned member values).

include_example(exercises/transpose2.c)


## Arrays and loops

Another common datatype in C is arrays. Reasoning about memory ownership for arrays is more difficult than for the datatypes we have seen so far: C allows the programmer to access arrays using *computed pointers*, and the size of an array does not need to be known as a constant at compile time. 

To support reasoning about code manipulating arrays and computed pointers CN has *iterated resources*. For instance, to specify ownership of an `int` array with 10 cells starting at pointer `p`, CN uses the iterated resource

```c
each (i32 i; 0i32 <= i && i < 10i32) 
     { Owned<int>(array_shift<int>(p,i)) }
```

In detail, this can be read as follows:

- for each integer `i` of CN type `i32`, ...

- if `i` is between `0` and `10`, ...

- assert ownership of a resource `Owned<int>` ...

- for cell `i` of the array with base-address `p`.

Here `array_shift<int>(p,i)` computes a pointer into the array at pointer `p`, appropriately offset for index `i`.

In general, iterated resource specifications take the form

```c
each (BT Q; GUARD) { RESOURCE }
```

comprising three parts:

- `BT Q`, for some CN type `BT` and name `Q`, introduces the quantifier `Q` of basetype `BT`, which is bound in `GUARD` and `RESOURCE`;

- `GUARD` is a boolean-typed expression delimiting the instances of `Q` for which ownership is asserted; and

- any non-iterated CN resource `RESOURCE`.


### First array example

Let's see how this applies to a first example of an array-manipulating function. Function `read` takes three arguments: the base pointer `p` of an `int` array, the length `n` of the array, and an index `i` into the array; `read` then returns the value of the `i`-th array cell.

include_example(exercises/array_load.broken.c)

The CN precondition requires ownership of the array on entry --- an iterated `Owned<int>` resource, one for each array index between `0` and `n` --- and that `i` lies within the range of owned indices. On return the array ownership is returned again. 

This specification, in principle, should ensure that the access `p[i]` is safe. However, running CN on the example produces an error: CN is unable to find the required ownership for reading `p[i]`.

```
cn build/solutions/array_load.broken.c
[1/1]: read
build/solutions/array_load.broken.c:5:10: error: Missing resource for reading
  return p[i];
         ^~~~
Resource needed: Owned<signed int>(array_shift<signed int>(p, (u64)i))
```

The reason is that when searching for a required resource CN's resource inference does not consider iterated resources (such as the required `Owned` resource for `p[i]` here). Quantifiers, such as used by iterated resources, can make verification undecidable, so, in order to maintain predictable type checking, CN delegates this aspect of the reasoning to the user. 

To make the (single) `Owned` resource required for accessing `p[i]` available to CN's resource inference we have to "extract" ownership for index `i` out of the iterated resource. 

include_example(exercises/array_load.c)

Here the CN comment `/*@ extract Owned<int>, i; @*/` is a CN "ghost statement"/proof hint that instructs CN to instantiate any available iterated `Owned<int>` resource for index `i`. In our example this operation splits the iterated resource into two:

```c
each(i32 j; 0i32 <= j && j < n) { Owned<int>(array_shift<int>(p,j)) }
```
is split into

1. the instantiation of the iterated resource at `i`

    ```c
    Owned<int>(array_shift<int>(p,i))
    ```

2. the remainder of the iterated resource, the ownership for all indices except `i`

    ```c
    each(i32 j; 0i32 <= j && j < n && j != i) 
        { Owned<int>(array_shift<int>(p,j)) }
    ```
   
   
After this extraction step, CN can use the (former) extracted resource to justify the access `p[i]`. 

Moreover, following an `extract` statement, CN remembers the extracted index and can automatically "reverse" the extraction when needed: after type checking the access `p[i]` CN must ensure the function's postcondition holds, which needs the full array ownership again (including the extracted index `i`); CN then automatically merges resources (1.) and (2.) again to obtain the required full array ownership, and completes the verification of the function.

So far the specification only guarantees safe execution but does not specify the behaviour of `read`. To address this, let's return to the iterated resources in the function specification. When we specify `take a1 = each ...` here, what is `a1`? In CN, the output of an iterated resource is a *map* from indices to resource outputs. In this example, where index `j` has CN type `i32` and the iterated resource is `Owned<int>`, the output `a1` is a map from `i32` indices to `i32` values --- CN type `map<i32,i32>`. (If the type of `j` was `i64` and the resource `Owned<char>`, `a1` would have type `map<i64,u8>`.)

We can use this to refine our specification with information about the functional behaviour of `read`.

include_example(exercises/array_load2.c)

We specify that `read` does not change the array --- the outputs `a1` and `a2`, before resp. after running the function, are the same --- and that the value returned is `a1[i]`, `a1` at index `i`.

### Exercise

**Array read two.** Specify and verify the following function, `array_read_two`, which takes the base pointer `p` of an `unsigned int` array, the array length `n`, and two indices `i` and `j`. Assuming `i` and `j` are different, it returns their sum.

  include_example(exercises/add_two_array.c)


**Swap array.** Specify and verify `swap_array`, which swaps the values of two cells of an `int` array. Assume again that `i` and `j` are different, and describe the effect of `swap_array` on the array value using the CN map update expression: `a[i:v]` denotes the same map as `a`, except with index `i` updated to `v`.

  include_example(exercises/swap_array.c)

### Loops

Array-manipulating functions 


## TODO: Datastructures and resource predicates: linked lists

C linked list example. This requires a different ownership pattern from before because the structure is recursive. Introduce **resource predicates** for ownership of recursive datastructures.

Example of CN linked list resource predicate without output ("ignore `void` return"). Verify safety of some simple list manipulating functions? List length?

Feeing all elements of a list (HLMC).


CN's **resource inference for resource predicates** unfolds resource predicates automatically as new information is learned about the inputs. Show with an example, ideally where this unfolding is not available at first, but then works after branching on whether the input pointer is null.

Maybe also show **manual case splitting**?


### TODO: CN datatypes and logical functions

For going beyond safety proofs there needs to be a way to refer to the data represented in memory. User-defined resource predicates have user-defined outputs that return information derived from inputs and owned memory. For instance, resource predicate that returns length or sum of the list as output (VeriFast?).

We need a way to talk about recursive data in specifications. Define CN list **datatype** and **CN pattern matching**. Modify linked list predicate to output the represented list.

Verify C implementations of list nil, cons, head, tail, with functional specification (HLMC?). (For the following: HLMC linked list library?)

For more complicated operations there needs to be a way to express recursive definitions on lists: introduce **(recursive) specification functions** .

Define CN list append, zero'ing out a list. Summing all the values and computing the length of a list? (VeriFast) -- so far without matching C functions.

Recursive CN functions cannot be handled automatically in proof. CN only knows f(args) = f(args') when args = args' for recursive functions, nothing else.

Show list append example, written as recursive C function, where **unfold** is used to unfold the definition of a recursive specification function to verify the example. Do the same for zeroing out, summing up the values, counting the list.

In all cases the C function should have a recursive structure matching the CN logical function, so unfolding works well.



### TODO: Loops, loop invariants, lemmata

Alternative formulation of list append using a while loop. This requires a loop invariant: basically this works the same as function preconditions, but more variables are in scope and function arguments are mutable.

To phrase the specification we need a predicate for partial linked lists/linked list segments. Verify list append safey without functional correctness; maybe other examples.

When we move to functional correctness we'll find that often `unfold` does not work, because the shape of the loop does not align nicely with the recursion of the specification function.

Instead, inductive reasoning is required, and we need to **specify and apply lemmata**. Apply that to the append example. (There's also the option of VeriFast-style C programs as proofs?)


### TODO: Binary trees?


## TODO: Iterated resources and quantified constraints

CN computed pointers and aliasing?

Now move to arrays, and explain **iterated resources**, first using just Owned.

Verify safety of some simple example program that loops over an array. Specify the ownership using iterated resources. CN rejects the program; fix by adding `extract`.

Verify a functional property of the same code. The **output of an iterated resource** is a map from indices to values.


Reasoning about functional properties of an array may require specifying properties that hold for all values of an array: we need **logical quantifiers**.

Specify such a property using quantifiers, and show how to **instantiate** it manually using `instantiate`.



