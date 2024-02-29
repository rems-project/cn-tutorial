include(src/setup.m4)




---
title: CN tutorial
fontsize: 18px
mainfont: sans-serif
linestretch: 1.4
maxwidth: 45em
---



CN is a type system for verifying C code, focusing especially on low-level systems code. Compared to the normal C type system, CN checks not only that expressions and statements follow the correct typing discipline for C-types, but also that the C code executes *safely* --- does not raise C undefined behaviour --- and *correctly* --- according to strong user-defined specifications. To accurately handle the complex semantics of C, CN builds on the [Cerberus semantics for C](https://github.com/rems-project/cerberus/).


## Installation 


To fetch and install CN, check the Cerberus repository at <https://github.com/rems-project/cerberus> and follow the instructions in [`backend/cn/INSTALL.md`](https://github.com/rems-project/cerberus/blob/master/backend/cn/INSTALL.md).

Type `cn --help` in your terminal to ensure CN is installed and found by your system. This should print the list of available options CN can be executed with. To apply CN to a C file, run `cn CFILE`. 




## Basic usage


For a first example, consider the simple function `add`, below, which takes two `int` arguments, `x` and `y`, and returns their sum. 

include_example(exercises/0.c)


In C `x+y` is only safe to execute when it is guaranteed that the result of the addition can be represented at type `int`: `x` and `y` are signed integers, and signed integer overflow and underflow are undefined behaviour (UB) in C. Running CN on the example therefore raises an error:

```
cn exercises/0.c
[1/1]: add
exercises/0.c:3:10: error: Undefined behaviour
  return x+y;
         ~^~
an exceptional condition occurs during the evaluation of an expression (§6.5#5)
Consider the state in /var/folders/_v/ndl32wpj4bb3y9dg11rvc8ph0000gn/T/state_393431.html
```

CN flags the undefined behaviour, pointing to the relevant source location and the paragraph of the C standard that specifies the undefined behaviour. The error message also includes a link to an HTML file, shown below, which includes more details on the error.

![CN error report](src/images/0.error.png)

### Error reports

Since diagnosing errors is an important part of using CN, let's take a closer look. The error report consists of two sections:

- The first section ("Path to error") contains information about the  control-flow path leading up to the error. 

  When type checking a C function, CN checks each possible control-flow path through the program individually. If CN detects UB or a violation of user-defined specifications, CN reports the problematic control-flow path. A path is reported as a nested structure of statements: paths are split into sections, grouping together statements between high-level control-flow positions (e.g. the start of the function, the start of a loop, the invocation of a `continue`, `break`, or `return` statement, etc.); within each section, the statements are given by their source location in the input file; finally CN reports, per statement, the typechecked sub-expressions, as well as the memory accesses and function calls within these.

  In our example, there is only one possible control-flow path: entering the function body (section "function body") and executing the block from lines 2 to 4, followed by the return statement at line 3. The entry for the latter contains the sequence of sub-expressions in the return statement, including reads of the variables `x` and `y`. 

  **Note.**  In C, a function's local variables, including the function arguments, are mutable and their address can be taken and passed as a value. CN (following Cerberus) therefore represents local variables as memory allocations that are manipulated using memory reads and writes. 
  
  CN's type checking of the return statement therefore involves checking memory reads for `x` and `y`, at their memory locations, which CN names `&ARG0` and `&ARG1`. The first read, at `&ARG0`, here returns the value `x` (that is, the value for `x` originally passed into the function `add`); the second read, at `&ARG1`, returns `y`. 
  
  Alongside this symbolic information, CN also displays concrete values: `1073741825i32 /* 0x40000001 */` for x (here the first value is the decimal representation and the second, in `/*...*/` comments the hex number) and `1073741824i32 /* 0x40000000 */` for `y`. (CN also displays values for the pointers, `{@0; 4}` for `x` and `{@0; 0}` for `y`, which we ignore for now.) 
  
  These values are part of a counter example, a concrete valuation of pointers and variables in the program that is consistent with the control flow path taken (and any user-specified assumptions), which leads to the error. The exact values may vary on your machine and also depend on the version of Z3 installed on your system.

- The second section, below the error trace, lists the verification context CN has reached along this control-flow path. 

  "Available resources" lists the owned resources before the error occurred, such as resources for owned pointers, as discussed later. 
  
  "Variables" lists counterexample values for program variables and their addresses. In addition to the variables `x` and `y`, which are assigned the same values as in the trace above, this includes possible values for the pointers `&ARG0` and `&ARG1` to their memory locations, as well as values for function pointers in scope and the `__cn_alloc_history`, both of which we ignore for now. 
  
  Finally, "Constraints" records all logical facts CN has learned before reaching the error. This includes any user-specified assumptions from a precondition or loop invariant, value range constraints for variables and function pointers implied by their C-types, and facts CN has learned during the type checking of the current control-flow path. 
  
  In this example, the only constraints are value range constraints for variables and functions in scope: e.g. 

    - `good<signed int>(x)` says that the initial value of function argument `x` is a "good" `signed int` value, that is, within the representable range of a C `signed int` value. For C integer types `T`, `good<T>` requires that the argument is representable at C-type `T`; for pointers `good` additionally requires that the argument is aligned with respect to the pointee type; for C structs `good` requires all members to be `good`, for arrays that all array cells have `good` values.

    - `repr<signed int*>(&ARGO)` records that the pointer to the memory location storing the first function argument, `x`, is representable at C-type `signed int*`; 
    
    - `aligned(&ARGO, 4u64)`, moreover, states that the same pointer is 4-byte aligned.





### Back to the example


From the error message we know the problematic expression is the addition `x+y`, and the counterexample values read for `x` and `y` give us a hint for how a concrete error case looks like: for very large values for `x` and `y` their sum can exceed the maximum representable `int` value: $1073741825 + 1073741824 = 2^31+1$. The function `add` only executes safely when called for smaller values. Similarly, *large negative* values of `x` and `y` can cause UB due to signed integer underflow, so these also have to be ruled out.

To ensure safe execution, we specify a precondition for add that constrains the ranges of `x` and `y`. Function specifications in CN are expressed using special `/*@ ... @*/` comments, placed between the function argument list and the function body.

include_example(solutions/0.c)

Preconditions are introduced using `requires`, which takes a list of one or more conditions, separated by semicolons. Here, to specify that the sum of `x` and `y` does not over- or underflow we assert that the sum of `x` and `y` is between $-2147483648$ and $2147483647$, the minimum and maximum `int` values, respectively. In detail:

- Function specifications can refer to the values of function arguments (here `x` and `y`). While function arguments are mutable in C; naming an argument in a function specification always refers to the *initial value* passed into the function.

- CN uses fixed width integer types to represent integer values, e.g. `u32` for 32-bit unsigned types and `i64` for signed 64-bit integers. When referring to C variables their C-type is mapped to the corresponding CN type. Here, `x` and `y` of C-type `int` get CN type `i32` (which, compared to the C-type, makes the width unambiguous).

- We cast the values of `x` and `y` to type `i64`, to add their values at this larger type, and let-bind the result to the name `sum`. Sum is then in scope everywhere in the remainder of the specification. 

- Finally, we constrain `x` and `y` so their sum is in the representable range. Constant integer values, such as `-2147483648i64`, are annotated with the sign and width of the integer type (`i64`).

Running CN on the annotated program passes with no errors. Which means we now know that `add` is safe to execute given this precondition. We might wish to additionally specify the *functional behaviour* of `add` and make a statement about its return values. We can do this by adding a postcondition using the `ensures` keyword.

include_example(solutions/1.c)

Here we specify that the function returns the sum of `x` and `y`: using the keyword `return`, which refers to the value returned by `add`, and `sum`, from the precondition (which is also in scope in the postcondition) we specify the return value is this `sum`, cast back to `i32` type. 

Running CN confirms that this postcondition also holds.


## Simple arithmetic

Let's apply what we know so far to another simple arithmetic example.

include_example(exercises/slf1_basic_example_let.signed.c)

Function `doubled` take an int `n`, defines `a` and `b` to be `n` incremented and decremented, respectively, and returns their sum. We would like to again verify safety, and prove that `doubled` returns the value of `n` doubled.

include_example(exercises/slf1_basic_example_let.signed.c)

Running CN flags UB for the increment of `a`. As in the first example, we need a precondition that ensures that `n+1` and `n-1` do not over-, respectively, underflow, and similarly the precondition has to ensure `a+b` is representable at `int` type.

include_example(solutions/slf1_basic_example_let.signed.c)

To specify these, we again work at a larger integer type: we cast `n` to type `i64` and specify that decrementing `n` does not go below the minimal `int` value, that incrementing `n` does not go above the maximal value, and that `n` doubled is within the right range. The post-condition specifies that `return` is double the value of `n`.


### Exercise

Specify the precondition needed to ensure safety of the C function `quadruple`, and a postcondition that describes its return value.

include_example(exercises/slf2_basic_quadruple.signed.c)



## Pointers and ownership

So far we've only considered example functions manipulating integer values. Verification becomes more interesting and challenging when *pointers* are involved, because the safety of memory accesses via pointers has to be verified.

CN uses *separation logic resource types* and the concept of *ownership* to reason about memory accesses. A resource is the permission to access a region of memory. Resources, are different from logical constraints in that resource ownership is *unique*, not duplicable. 

Let's look at a simple example function: `read` takes an `int` pointer `p` and returns the value.

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

CN reports that for the read `*p` to be safe, ownership of a resource is missing: a resource `Owned<signed int>(p)` (where `signed int` and `int` are the same C-type --- CN just makes the sign explicit).

### Owned

The resource `Owned<T>(p)`, for a C-type `T` and pointer `p`, asserts ownership of a memory cell at location `p` of the size of C-type `T`. It is is CN's equivalent of a points-to assertion in separation logic (indexed by C-types). 

In this example we can ensure the safe execution of `read` by adding a precondition that requires ownership of `Owned<int>(p)` (for now ignore the notation `take ... = Owned<int>(p)`). We also add a post-condition that specifies that on exiting the function `read`, ownership of `p` is returned in the form of another `Owned<int>(p)` resource.

include_example(solutions/read.c)

This specifications means that any function calling `read` has to be able to provide a resource `Owned<int>(p)` to pass to `read`, and will receive back a resource `Owned<int>(p)` when the function has finished executing.

### Resource outputs

A caller of `read` may wish to know that `read` leaves the value unchanged, so we need a way to refer to the pointee of `p`. 

In CN resources have *outputs*. Each resource outputs the information that can be derived from ownership of the resource. What information is returned is specific to the type of resource. The resource `Owned<T>(p)` (for some C-type `T`), for instance, outputs the *pointee value* of `p`, since can be derived from the resource ownership: assume you have a pointer `p` and associated ownership, then this uniquely determines the pointee value. 

The `take`-notation in the example above is used to bind the outputs of a resource to a name. Hence the precondition `take v1 = Owned<int>(p)`, in addition to asserting ownership, introduces the name `v1` for the output of `Owned<int>(p)`, the pointee value at the start of the function. Similarly, the postcondition introduces the name `v2` for the pointee value on returning from the function.

We can use the resource outputs to complete the example and specify that `read` leaves the pointee value of `p` unchanged, by adding the constraint `v1 == v2` in the postcondition.

include_example(solutions/read.c)


**Aside.** In standard separation logic the equivalent specification for `read` could have been phrased as follows:
```
{ ∃ v1. p ↦ v1 } read(p) { ∃ v2. ((p ↦ v2) * v1 = v2) }
```
CN's `take` notation is just an alternative syntax for existential quantification over the values of resources (e.g. `take v1 = Owned<...>(p)` vs. `∃ v1. p ↦ v1`), but a useful one: the `take` notation syntactically restricts how quantifiers can be used, so CN can always infer them.


### Block

Aside from the `Owned` resource seen above, CN has another built-in resource type: `Block`. For a C-type `T` and pointer `p`, `Block<T>(p)` asserts the same ownership as `Owned<T>(p)` (so ownership of a memory cell at `p`, the size of type `T`), but in contrast to `Owned`, `Block` does not assert that the memory cell is initialised. CN uses this distinction to prevent reads from uninitialised memory: 

- A read at C-type `T` and pointer `p` requires a resource `Owned<T>(p)`, so ownership of *initialised* memory at the right C-type. The load returns the resource unchanged.

- A write at C-type `T` and pointer `p` needs only a `Block<T>(p)` (so, unlike reads, writes to uninitialised memory are fine). The write consumes ownership of the resource (it destroys it) and returns a new resource `Owned<T>(p)` with appropriate output. Hence the returned resource records the fact that the memory cell is now initialised and can be read from.

Since `Owned` carries the same ownership as `Block`, a resource `Owned<T>(p)` can be used in place of `Block<T>(p)`: for instance the typing of a write requires `Block<T>(p)`, but can just as well be satisfied with a matching `Owned<T>(p)` resource. (Intuitively, an already-initialised memory call can, of course, be written again.)

Unlike `Owned`, which outputs the pointee value, `Block` has no meaningful output: its output is `void`/`unit`.


### Write example

Let's test resources and their outputs in another example. The C function `incr` takes an `int` pointer `p` and increments the pointee value. 

include_example(solutions/slf0_basic_incr.signed.c)

In the precondition we assert ownership of resource `Owned<int>(p)`, binding its output/pointee value to `v1`, and use `v1` to specify that the pointee value of `p` must be sufficiently small at the start of the function not to overflow when incremented. The postcondition again asserts ownership for `p`, with output `v2`, and uses this to relate the initial pointee value, `v1` with the incremented final value, `v2` (`v2 == v1+1i32`).


If we specified `Block<int>(p)` instead of `Owned<int>(p)` in the precondition, as in the *incorrect* specification below, then CN would reject the program.

include_example(solutions/slf0_basic_incr.signed.broken.c)

CN then reports:
```
build/solutions/slf0_basic_incr.signed.broken.c:6:11: error: Missing resource for reading
  int n = *p;
          ^~
Resource needed: Owned<signed int>(p)
Consider the state in /var/folders/_v/ndl32wpj4bb3y9dg11rvc8ph0000gn/T/state_5da0f3.html
```

The `Owned<int>(p)` resource required for reading is missing, since, as per precondition, only `Block<int>(p)` is available. Checking the linked HTML file confirms this. Here the section "Available resources" lists all resource ownership at the point of the failure:

- `Block<signed int>(p)(u)`, the ownership of uninitialised memory at location `p`; its output is the `void`/`unit` value `u` (specified in the second pair of parentheses)

- `Owned<signed int*>(&ARG0)(p)`, the ownership of (initialised) memory at location `&ARG0`, so the memory location where the first function argument is stored; its output is the pointer `p` (not to be confused with the pointee of `p`); and finally

- `__CN_Alloc(&ARG0)(void)` is a resource that records allocation information for location `&ARG0`; this is related to CN's memory-object semantics, which we skip over for the moment.


### Exercises

Give a specification for the function `inplace_double`, which takes an `int` pointer `p` and doubles the pointee value: specify the precondition needed to guarantee safe execution and a postcondition that captures the function's behaviour.

include_example(exercises/slf3_basic_inplace_double.c)
