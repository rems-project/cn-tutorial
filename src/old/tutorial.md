# CN tutorial

_By Christopher Pulte and Benjamin C. Pierce, with contributions from Elizabeth Austell._

CN is an extension of the C programming language for verifying the correctness of C code, especially on low-level systems code. Compared to standard C, CN checks not only that expressions and statements follow the correct typing discipline for C-types, but also that the C code executes _safely_ — does not raise C undefined behaviour — and _correctly_ — satisfying to strong, user-defined specifications.
This tutorial introduces CN through a series of examples, starting with basic usage of CN on simple arithmetic functions and slowly moving towards more elaborate separation logic specifications of data structures.

This tutorial is a work in progress -- your suggestions are greatly appreciated!

**Origins.**
CN was first described in [CN: Verifying Systems C Code with Separation-Logic Refinement Types](https://dl.acm.org/doi/10.1145/3571194) by Christopher Pulte, Dhruv C. Makwana, Thomas Sewell, Kayvan Memarian, Peter Sewell, and Neel Krishnaswami.
To accurately handle the complex semantics of C, CN builds on the [Cerberus semantics for C](https://github.com/rems-project/cerberus/).
Some of the examples in this tutorial are adapted from Arthur Charguéraud’s excellent
[Separation Logic Foundations](https://softwarefoundations.cis.upenn.edu) textbook, and one of the case studies is based on an
extended exercise due to Bryan Parno.

--

**Acknowledgment of Support and Disclaimer.**
This material is based upon work supported by the Air Force Research Laboratory (AFRL) and Defense Advanced Research Projects Agencies (DARPA) under Contract No. FA8750-24-C-B044, a European Research Council (ERC) Advanced Grant “ELVER” under the European Union’s Horizon 2020 research and innovation programme (grant agreement no. 789108), and additional funding from Google. The opinions, findings, and conclusions or recommendations expressed in this material are those of the authors and do not necessarily reflect the views of the Air Force Research Laboratory (AFRL).

## Installing CN

To fetch and install CN, visit the [Cerberus repository](https://github.com/rems-project/cerberus) and follow the instructions in [backend/cn/README.md](https://github.com/rems-project/cerberus/blob/master/backend/cn/README.md).

Once the installation is completed, type `cn --help` in your terminal to ensure CN is installed and found by your system. This should print the list of available options CN can be executed with.

To apply CN to a C file, run `cn verify CFILE`.

## Source files

The source files for all the exercises and examples below can be downloaded
from [here](link:exercises.zip).

## Basics

### First example

The simple arithmetic function: `add` shown below takes two `int` arguments, `x` and `y`, and returns their sum.

```c title="exercises/add_0.c"
--8<--
exercises/add_0.c
--8<--
```

Running CN on the example produces an error message:

```
cn verify exercises/add_0.c
[1/1]: add
exercises/add_0.c:3:10: error: Undefined behaviour
return x+y;
~^~
an exceptional condition occurs during the evaluation of an expression (§6.5#5)
Consider the state in /var/folders/\_v/ndl32rvc8ph0000gn/T/state_393431.html
```

CN rejects the program because it has _undefined behaviour_ according to the C standard, meaning it is not safe to execute. CN points to the relevant source location, the addition `x+y`, and paragraph §6.5#5 of the standard, which specifies the undefined behaviour. It also includes a link to an HTML file with more details on the error to help in diagnosing the problem.

Inspecting this HTML report (as we do in a moment) gives us possible example values for `x` and `y` that cause the undefined behaviour and hint at the problem: for very large values for `x` and `y`, such as `1073741825` and `1073741824`, the sum of `x` and `y` can exceed the representable range of a C `int` value: `1073741825 + 1073741824 = 2^31+1`, so their sum is larger than the maximal `int` value, `2^31-1`.

Here `x` and `y` are _signed integers_, and in C, signed integer _overflow_ is undefined behaviour (UB). Hence, `add` is only safe to execute for smaller values. Similarly, _large negative_ values of `x` and `y` can cause signed integer _underflow_, also UB in C. We therefore need to rule out too-large values for `x` and `y`, both positive and negative, which we do by writing a CN function specification.

### First function specification

Shown below is our first function specification, for `add`, with a precondition that constrains `x` and `y` such that the sum of `x` and `y` lies between `-2147483648` and `2147483647`, so within the representable range of a C `int` value.

```c title="solutions/add_0.c"
--8<--
solutions/add_0.c
--8<--
```

In detail:

- Function specifications are given using special `/*@ ... @*/` comments, placed in-between the function argument list and the function body.
  <!-- TODO: BCP: We should mention the alternative concrete syntax, when it is decided and implemented. -->
  <!-- Add CN flag '--magic-comment-char-dollar' to switch CN comment syntax to '/_$ ... $_/'. -->

- The keyword `requires` starts the precondition, a list of one or more CN conditions separated by semicolons.

- In function specifications, the names of the function arguments, here `x` and `y`, refer to their _initial values_. (Function arguments are mutable in C.)

- `let Sum = (i64) x + (i64) y` is a let-binding, which defines `Sum` as the value `(i64) x + (i64) y` in the remainder of the function specification.

- Instead of C syntax, CN uses Rust-like syntax for integer types, such as `u32` for 32-bit unsigned integers and `i64` for signed 64-bit integers, to make their sizes unambiguous. Here, `x` and `y`, of C-type `int`, have CN type `i32`.
  <!-- TODO: BCP: I understand this reasoning, but I wonder whether it introduces more confusion than it avoids -- it means there are two ways of writing everything, and people have to remember whether the particular thing they are writing right now is C or CN... -->
  <!-- BCP: Hopefully we are moving toward unifying these notations anyway? -->

- To define `Sum` we cast `x` and `y` to the larger `i64` type, using syntax `(i64)`, which is large enough to hold the sum of any two `i32` values.

- Finally, we require this sum to be between the minimal and maximal `int` values. Integer constants, such as `-2147483648i64`, must specifiy their CN type (`i64`).
  <!-- TODO: BCP: We should use the new ' syntax (or whatever it turned out to be) for numeric constants -->
  <!-- Dhruv: Yet to be implemented: rems-project/cerberus#337 -->

Running CN on the annotated program passes without errors. This means that, with our specified precondition, `add` is safe to execute.

We may, however, wish to be more precise. So far, the specification gives no information to callers of `add` about its output. To describe its return value we add a postcondition to the specification using the `ensures` keyword.

```c title="solutions/add_1.c"
--8<--
solutions/add_1.c
--8<--
```

Here we use the keyword `return`, which is only available in function
postconditions, to refer to the return value, and we equate it to `Sum`
as defined in the precondition, cast back to `i32` type: that is, `add`
returns the sum of `x` and `y`.

Running CN confirms that this postcondition also holds.

One final refinement of this example. CN defines constant functions `MINi32`, `MAXi64`, etc. so that specifications do not need to be littered with unreadable numeric constants.

```c title="solutions/add_2.c"
--8<--
solutions/add_2.c
--8<--
```

Two things to note: (1) These are constant _functions_, so they
require a following `()`. And (2) The type of `MINi32()` is `i32`, so
if we want to use it as a 64-bit constant we need to add the explicit
coercion `(i64)`.

### Error reports

In the original example, CN reported a type error due to C undefined
behaviour. While that example was perhaps simple enough to guess the
problem and solution, this can become quite challenging as program and
specification complexity increases. Diagnosing errors is
therefore an important part of using CN. CN tries to help with this by
producing detailed error information, in the form of an HTML error
report.

Let’s return to the type error from earlier -- `add` without
precondition -- and take a closer look at this report.

_CN error report_
![*CN error report: 0*](images/0_error.png)

_Definitions and constraints not handled automatically_

CN checks that the code matches its specification with the help of an SMT
solver. CN passes a set of constraints along with program context to the SMT
solver, which either confirms that a given constraint will always hold in
that program context, provides a counterexample in which the constraint does
not hold, or times out. To avoid timeouts, CN avoids passing some definitions
to the solver, including recursive functions, some predicates with branching,
and constraints with `forall`. The error file displays in this section which
definitions and constraints CN did not pass to the solver.

_Resources that do not satisfy predicate definitions_

Because CN does not pass certain definitions to the solver, it may return
spurious counterexamples that do not respect those definitions. Consider this
example:

![*CN error report: string*](images/string_error.png)

`String` is a predicate representing a null-terminated string.
In general, CN does not know how much to unfold the mutually recursive
predicates `String` and `StringAux`, so it does not pass their full
definition to the solver. This leads to a spurious counterexample: `sIn` is the
singleton string containing exactly the null character `0u8`. This is
impossible; the predicate leaves out the null when constructing the logical
representation of a string. To make clear that this is a bad counterexample,
the error file lists `String(s) (sIn)` under _Resources that do not satisfy
predicate definitions_.

<!-- TODO: BCP: It looks quite different now! -->

_Path to error._ The first section contains information about the
control-flow path leading to the error.

When checking a C function, CN examines each possible control-flow
path individually. If it detects UB or a violation of user-defined
specifications, CN reports the problematic control-flow path as a
nested structure of statements: the path is split into sections that
group together statements between high-level control-flow positions
(e.g. function entry, the start of a loop, the invocation of a
`continue`, `break`, or `return` statement, etc.); within each
section, statements are listed by source code location; finally, per
statement, CN lists the typechecked sub-expressions, and the memory
accesses and function calls within these.

In our example, there is only one possible control-flow path: entering
the function body (section "`function body`") and executing the W
from lines 2 to 4, followed by the return statement at line 3. The
entry for the latter contains the sequence of sub-expressions in the
return statement, including reads of the variables `x` and `y`.

In C, local variables in a function, including its arguments, are
mutable, their addresses can be taken and passed as values. CN
therefore represents local variables as memory allocations that are
manipulated using memory reads and writes. Here, type checking the
return statement includes checking memory reads for `x` and `y`,
at their locations `&ARG0` and `&ARG1`. The path report lists
these reads and their return values: the read at `&ARG0` returns
`x` (that is, the value of `x` originally passed to `add`); the
read at `&ARG1` returns `y`. Alongside this symbolic information,
CN displays concrete values:

- `1073741825i32 /* 0x40000001 */` for x (the first value is the decimal representation, the second, in `/*...*/` comments, the hex equivalent) and

- `1073741824i32 /* 0x40000000 */` for `y`.

For now, ignore the pointer values `{@0; 4}` for `x` and `{@0; 0}` for `y`.

<!-- TODO: BCP: Where are these things discussed? Anywhere? (When) are they useful? -->
<!-- Dhruv: These are part of VIP memory model things I'm working on, which will hopefully be implemented and enabled in the next few weeks. -->

These concrete values are part of a _counterexample_: a concrete
valuation of variables and pointers in the program that that leads to
the error. (The exact values may vary on your machine, depending on
the SMT solver -- i.e., the particular version of Z3, CVC5, or
whatever installed on your system.)

_Proof context._ The second section, below the error trace, lists the proof context CN has reached along this control-flow path.

"`Available resources`" lists the RW resources, as discussed in later sections.

"`Variables`" lists counterexample values for program variables and pointers. In addition to `x` and `y`, assigned the same values as above, this includes values for their memory locations `&ARG0` and `&ARG1`, function pointers in scope, and the `__cn_alloc_history`, all of which we ignore for now.

<!-- TODO: BCP: Again, where are these things discussed? Should they be? -->
<!-- Dhruv: Also VIP. -->

Finally, "`Constraints`" records all logical facts CN has learned along the path. This includes user-specified assumptions from preconditions or loop invariants, value ranges inferred from the C-types of variables, and facts learned during the type checking of the statements. Here -- when checking `add` without precondition -- the only constraints are those inferred from C-types in the code:

- For instance, `good<signed int>(x)` says that the initial value of
  `x` is a "`good`" `signed int` value (i.e. in range). Here
  `signed int` is the same type as `int`, CN just makes the sign
  explicit.
  <!-- TODO: BCP: Yikes! This seems potentially confusing -->

  For an integer type `T`, the type `good<T>` requires the value to
  be in range of type `T`; for pointer types `T`, it also requires
  the pointer to be aligned. For structs and arrays, this extends in the
  obvious way to struct members or array cells.
  <!-- TODO: BCP: Is this information actually ever useful? Is it currently suppressed? -->

- `repr<T>` requires representability (not alignment) at type `T`, so `repr<signed int*>(&ARGO)`, for instance, records that the pointer to `x` is representable at C-type `signed int*`;

- `aligned(&ARGO, 4u64)`, moreover, states that it is 4-byte aligned.

<!-- TODO: URGENT: BCP: Some of the above (especially the bit at the end) feels like TMI for many/most users, especially at this point in the tutorial. -->
<!-- Dhruv: Probably true, we actually even hide some of these by default. -->
<!-- BCP: I propose we hide the rest and move this discussion to somewhere else ("Gory Details" section of the tutorial, or better yet reference manual). -->
<!-- Dhruv: Thumbs up -->

### Another arithmetic example

Let’s apply what we know so far to another simple arithmetic example.

The function `doubled`, shown below, takes an int `n`, defines `a` as `n` incremented, `b` as `n` decremented, and returns the sum of the two.

<!-- TODO: BCP: Is it important to number the slf examples? If so, we should do it consistently, but IMO it is not. Better to rename them without numbers. -->

```c title="exercises/slf1_basic_example_let.signed.c"
--8<--
exercises/slf1_basic_example_let.signed.c
--8<--
```

We would like to verify this is safe, and that `doubled` returns twice the value of `n`. Running CN on `doubled` leads to a type error: the increment of `a` has undefined behaviour.

As in the first example, we need to ensure that `n+1` does not overflow and `n-1` does not underflow. Similarly `a+b` has to be representable at `int` type.

```c title="solutions/slf1_basic_example_let.signed.c"
--8<--
solutions/slf1_basic_example_let.signed.c
--8<--
```

<!-- TODO: BCP: WHy n*+n\_ in some places and n\*2i32 in others? -->
<!-- Dhruv: Unlikely to be meaningful, either is fine. -->

We encode these expectations using a similar style of precondition as in the first example. We first define `N` as `n` cast to type `i64` — i.e. a type large enough to hold `n+1`, `n-1`, and `a+b` for any possible `i32` value for `n`. Then we specify that decrementing `N` does not go below the minimal `int` value, that incrementing `N` does not go above the maximal value, and that `n` doubled is also in range. These preconditions together guarantee safe execution.

<!-- TODO: BCP: How about renaming N to n64? -->
<!-- Dhruv: Sensible. -->
<!-- BCP: (someone do it on next pass) -->

To capture the functional behaviour, the postcondition specifies that `return` is twice the value of `n`.

### Exercises

_Quadruple._ Specify the precondition needed to ensure safety of the C function `quadruple`, and a postcondition that describes its return value.

```c title="exercises/slf2_basic_quadruple.signed.c"
--8<--
exercises/slf2_basic_quadruple.signed.c
--8<--
```

_Abs._ Give a specification to the C function `abs`, which computes the absolute value of a given `int` value. To describe the return value, use CN’s ternary "`_ ? _ : _`" operator. Given a boolean `b`, and expressions `e1` and `e2` of the same basetype, `b ? e1 : e2` returns `e1` if `b` holds and `e2` otherwise.
Note that most binary operators in CN have higher precedence than the ternary operator, so depending on your solution you may need to place the ternary expression in parentheses.

```c title="exercises/abs.c"
--8<--
exercises/abs.c
--8<--
```

## Pointers and simple ownership

So far we’ve only considered example functions manipulating integer values. Verification becomes more interesting and challenging when _pointers_ are involved, because the safety of memory accesses via pointers has to be verified.

CN uses _separation logic resources_ and the concept of _ownership_ to reason about memory accesses. A resource is the permission to access a region of memory. Unlike logical constraints, resource ownership is _unique_, meaning resources cannot be duplicated.

Let’s look at a simple example. The function `read` takes an `int` pointer `p` and returns the pointee value.

```c title="exercises/read.c"
--8<--
exercises/read.c
--8<--
```

Running CN on this example produces the following error:

```
cn verify exercises/read.c
[1/1]: read
exercises/read.c:3:10: error: Missing resource for reading
return \*p;
^~
Resource needed: RW<signed int>(p)
Consider the state in /var/folders/\_v/ndl32wpj4bb3y9dg11rvc8ph0000gn/T/state_403624.html
```

For the read `*p` to be safe, ownership of a resource is missing: a resource `RW<signed int>(p)`.

### RW resources

<!-- TODO: BCP: Perhaps this is a good time for one last discussion of the keyword "RW", which I have never found very helpful: the resource itself isn't RW -- it's a description of something that _can_ be RW. (It's "take" that does the owning.) Moreover, "RW" and "W" are badly non-parallel, both grammatically and semantically. I suggest "Resource" instead of "RW". (We can keep "W" -- it's not too bad, IMO.) -->

<!--
Dhruv:
We use the word "resources" to describe any "resource predicate" RW, or user-defined, (and eventually live allocations and locks) so I'm not sure that suggestion works any better. It is just a points-to with read and write permissions, so perhaps a RW(p)? (or ReadWrite(p)?).

@bcpierce00
Both of these are better than RW!

(And then W can become WriteOnly.)

BCP: I think this discussion is reflected in the GitHub exchange
-->

Given a C-type `T` and pointer `p`, the resource `RW<T>(p)` asserts ownership of a memory cell at location `p` of the size of C-type `T`. It is CN’s equivalent of a points-to assertion in separation logic (indexed by C-types `T`).

In this example we can ensure the safe execution of `read` by adding a precondition that requires ownership of `RW<int>(p)`, as shown below. For now ignore the notation `take ... = RW<int>(p)`. Since reading the pointer does not disturb its value, we also add a corresponding postcondition, whereby `read` returns ownership of `p` after it is finished executing, in the form of another `RW<int>(p)` resource.

```c title="solutions/read.c"
--8<--
solutions/read.c
--8<--
```

This specification means that:

- any function calling `read` has to be able to provide a resource `RW<int>(p)` to pass into `read`, and

- the caller will receive back a resource `RW<int>(p)` when `read` returns.

### Resource outputs

A caller of `read` may also wish to know that `read` actually returns the correct value, the pointee of `p`, and also that it does not change memory at location `p`. To phrase both we need a way to refer to the pointee of `p`.

<!-- TODO: BCP: The idea that "resources have outputs" is very mind-boggling to many new users, _especially_ folks with some separation logic background. Needs to be explained very carefully. Also, there's some semantic muddle in the terminology: Is a resource (1) a thing in the heap, (2) a thing in the heap that one is currently holding, or (3) the act of holding a thing in the heap? These are definitely not at all the same thing, but our language at different points suggests all three! To me, (1) is the natural sense of the word "resource"; (2) is somewhat awkward, and (3) is extremely awkward. -->

In CN, resources have _outputs_. Each resource outputs the information that can be derived from ownership of the resource. What information is returned is specific to the type of resource. A resource `RW<T>(p)` (for some C-type `T`) outputs the _pointee value_ of `p`, since that can be derived from the resource ownership: assume you have a pointer `p` and the associated ownership, then this uniquely determines the pointee value of `p`.

<!-- TODO: BCP: ... in a given heap! (The real problem here is that "and the associated ownership" is pretty vague.) -->
<!-- Dhruv: Perhaps mentioning sub-heaps will help? -->

CN uses the `take`-notation seen in the example above to bind the output of a resource to a new name. The precondition `take P = RW<int>(p)` does two things: (1) it assert ownership of resource `RW<int>(p)`, and (2) it binds the name `P` to the resource output, here the pointee value of `p` at the start of the function. Similarly, the postcondition introduces the name `P_post` for the pointee value on function return.

<!-- TODO: BCP: But, as we've discussed, the word "take" in the postcondition is quite confusing: What it's doing is precisely the _opposite_ of "taking" the resournce, not taking it but giving it back!! It would be much better if we could choose a more neutral word that doesn't imply either taking or giving. E.g. "resource". -->

<!-- TODO: BCP: This might be a good place for a comment on naming conventions. Plus a pointer to a longer discussion if needed -->

That means we can use the resource outputs from the pre- and postcondition to strengthen the specification of `read` as planned. We add two new postconditions specifying

1. that `read` returns `P` (the initial pointee value of `p`), and
1. that the pointee values `P` and `P_post` before and after execution of `read` (respectively) are the same.

```c title="exercises/read2.c"
--8<--
exercises/read2.c
--8<--
```

_Aside._ In standard separation logic, the equivalent specification for `read` could have been phrased as follows (where `\return` binds the return value in the postcondition):

<!-- TODO: Sainati: as a separation logic noob, I would love a more detailed explanation about what is going on here. -->

<!-- Why do we need to have v2 existentially quantified, for example, when p is only pointing to a single value? -->

```
∀p.
∀v1.
{ p ↦ P }
read(p)
{ \return. ∃P_post. (p ↦ P_post) /\ return = P /\ P = P_post }
```

CN’s `take` notation is just an alternative syntax for quantification over the values of resources, but a useful one: the `take` notation syntactically restricts how these quantifiers can be used to ensure CN can always infer them.

### Linear resource ownership

In the specifications we have written so far, functions that receive resources as part of their precondition also return this ownership in their postcondition.

Let’s try the `read` example from earlier again, but with a postcondition that does not return the ownership:

```c title="exercises/read.broken.c"
--8<--
exercises/read.broken.c
--8<--
```

CN rejects this program with the following message:

```
cn verify exercises/read.broken.c
[1/1]: read
build/exercises/read.broken.c:4:3: error: Left_Sublist-over unused resource 'RW<signed int>(p)(v1)'
return \*p;
^~~~~~~~~~
Consider the state in /var/folders/\_v/ndl32wpj4bb3y9dg11rvc8ph0000gn/T/state_17eb4a.html
```

CN has typechecked the function and verified (1) that it is safe to
execute under the precondition (given ownership `RW<int>(p)`)
and (2) that the function (vacuously) satisfies its postcondition. But
following the check of the postcondition it finds that not all
resources have been "`used up`".

Indeed, given the above specification, `read` leaks memory: it takes ownership, does not return it, but also does not deallocate the RW memory or otherwise dispose of it. In CN this is a type error.

CN’s resources are _linear_. This means not only that resources cannot be duplicated, but also that resources cannot simply be dropped or "`forgotten`". Every resource passed into a function has to be either _returned_ to the caller or else _destroyed_ by deallocating the RW area of memory (as we shall see later).

CN’s motivation for linear tracking of resources is its focus on
low-level systems software in which memory is managed manually; in
this context, memory leaks are typically very undesirable. As a
consequence, function specifications have to do precise bookkeeping of
their resource footprint and, in particular, return any unused
resources back to the caller.

### Exercises

_Quadruple_. Specify the function `quadruple_mem`, which is similar to the earlier `quadruple` function, except that the input is passed as an `int` pointer. Write a specification that takes ownership of this pointer on entry and returns this ownership on exit, leaving the pointee value unchanged.

```c title="exercises/slf_quadruple_mem.c"
--8<--
exercises/slf_quadruple_mem.c
--8<--
```

_Abs_. Give a specification to the function `abs_mem`, which computes the absolute value of a number passed as an `int` pointer.

```c title="exercises/abs_mem.c"
--8<--
exercises/abs_mem.c
--8<--
```

### W resources

Aside from the `RW` resources seen so far, CN has another
built-in type of resource called `W`. Given a C-type `T` and
pointer `p`, `W<T>(p)` asserts the same ownership as
`RW<T>(p)` — ownership of a memory cell at `p` the size of type
`T` — but, in contrast to `RW`, `W` memory is not assumed
to be initialised.

CN uses this distinction to prevent reads from uninitialised memory:

- A read at C-type `T` and pointer `p` requires a resource
  `RW<T>(p)`, i.e., ownership of _initialised_ memory at the
  right C-type. The load returns the `RW` resource unchanged.

- A write at C-type `T` and pointer `p` needs only a
`W<T>(p)` (so, unlike reads, writes to uninitialised memory
are fine). The write consumes ownership of the `W` resource
(it destroys it) and returns a new resource `RW<T>(p)` with the
value written as the output. This means the resource returned from a
write records the fact that this memory cell is now initialised and
can be read from.
<!-- TODO: BCP: Not sure I understand "returns a new resource `RW<T>(p)` with the value written as the output" -- perhaps in part because I don't understand what the output of a resource means when the resource is not in the context o a take expression. -->

Since `RW` carries the same ownership as `W`, just with the
additional information that the `RW` memory is initalised, a
resource `RW<T>(p)` is "`at least as good`" as `W<T>(p)` —
an `RW<T>(p)` resource can be used whenever `W<T>(p)` is
needed. For instance CN’s type checking of a write to `p` requires a
`W<T>(p)`, but if an `RW<T>(p)` resource is what is
available, this can be used just the same. This allows an
already-initialised memory cell to be over-written again.

Unlike `RW`, whose output is the pointee value, `W` has no meaningful output.

### Writing through pointers

Let’s explore resources and their outputs in another example. The C function `incr` takes an `int` pointer `p` and increments the value in the memory cell that it poinbts to.

```c title="exercises/slf0_basic_incr.signed.c"
--8<--
exercises/slf0_basic_incr.signed.c
--8<--
```

In the precondition we assert ownership of resource `RW<int>(p)`,
binding its output/pointee value to `P`, and use `P` to specify
that `p` must point to a sufficiently small value at the start of
the function so as not to overflow when incremented. The postcondition
asserts ownership of `p` with output `P_post`, as before, and uses
this to express that the value `p` points to is incremented by
`incr`: `P_post == P + 1i32`.

If we incorrectly tweaked this specification and used `W<int>(p)` instead of `RW<int>(p)` in the precondition, as below, then CN would reject the program.

```c title="exercises/slf0_basic_incr.signed.broken.c"
--8<--
exercises/slf0_basic_incr.signed.broken.c
--8<--
```

CN reports:

```
build/solutions/slf0_basic_incr.signed.broken.c:6:11: error: Missing resource for reading
int n = \*p;
^~
Resource needed: RW<signed int>(p)
Consider the state in /var/folders/\_v/ndl32wpj4bb3y9dg11rvc8ph0000gn/T/state_5da0f3.html
```

The `RW<int>(p)` resource required for reading is missing, since, per the precondition, only `W<int>(p)` is available. Checking the linked HTML file confirms this. Here the section "`Available resources`" lists all resource ownership at the point of the failure:

- `W<signed int>(p)(u)`, i.e., ownership of uninitialised memory
  at location `p`; the output is a `void`/`unit` value `u`
  (specified in the second pair of parentheses)

- `RW<signed int*>(&ARG0)(p)`, the ownership of (initialised)
  memory at location `&ARG0`, i.e., the memory location where the
  first function argument is stored; its output is the pointer `p`
  (not to be confused with the pointee of `p`); and finally

- `__CN_Alloc(&ARG0)(void)` is a resource that records allocation
  information for location `&ARG0`; this is related to CN’s
  memory-object semantics, which we ignore for the moment.

<!-- TODO: BCP: These bullet points are all a bit mysterious and maybe TMI. More generally, we should double check that this is actually the information displayed in the current HTML output... -->
<!-- Dhruv: It is displayed, but hidden. And perhaps TMI right now, but once the memory model lands properly, will sadly be the price of entry to writing verifiable (semantically well-defined) C. -->

### Exercises

_Zero._ Write a specification for the function `zero`, which takes a pointer to _uninitialised_ memory and initialises it to `0`.

```c title="exercises/zero.c"
--8<--
exercises/zero.c
--8<--
```

_In-place double._ Give a specification for the function `inplace_double`, which takes an `int` pointer `p` and doubles the pointee value: specify the precondition needed to guarantee safe execution and a postcondition that captures the function’s behaviour.

```c title="exercises/slf3_basic_inplace_double.c"
--8<--
exercises/slf3_basic_inplace_double.c
--8<--
```

### Multiple RW pointers

When functions manipulate multiple pointers, we can assert their
ownership just like before. However
pointer ownership in CN is unique -- that is, simultaneously owning
`RW` or `W` resources for two pointers implies that these
pointers are disjoint.

The following example shows the use of two `RW` resources for
accessing two different pointers by a function `add`, which reads
two `int` values in memory, at locations `p` and `q`, and
returns their sum.

<!-- TODO: BCP: Hmmm -- I'm not very sure that the way I've been naming things is actually working that well. The problem is that in examples like this we computer "thing pointed to by p" at both C and CN levels. At the C level, the thing pointed to by p obviously cannot also be called p, so it doesn't make sense for it to be called P at the CN level, right? Maybe we need to think again, but hoinestly I am not certain that it is _not_ working either. So I'm going to opush on for now... -->

```c title="exercises/add_read.c"
--8<--
exercises/add_read.c
--8<--
```

OUTDATED:

This time we use C’s `unsigned int` type. In C, over- and underflow of unsigned integers is not undefined behaviour, so we do not need any special preconditions to rule this out. Instead, when an arithmetic operation at `unsigned int` type goes outside the representable range, the value "`wraps around`".

The CN variables `P` and `Q` (resp. `P_post` and `Q_post`) for the pointee values of `p` and `q` before (resp. after) the execution of `add` have CN basetype `u32`, so unsigned 32-bit integers, matching the C `unsigned int` type. Like C’s unsigned integer arithmetic, CN unsigned int values wrap around when exceeding the value range of the type.

Hence, the postcondition `return == P + Q` holds also when the sum of `P` and `Q` is greater than the maximal `unsigned int` value.

<!-- TODO: BCP: I wonder whether we should uniformly use i32 integers everywhere in the tutorial (just mentioning in the bullet list below that there are other integer types, and using i64 for calculations that may overflow). Forgetting which integer type I was using was a common (and silly) failure mode when I was first working through the tutorial. -->
<!-- Dhruv: Sensible. -->
<!-- BCP: ... On second thought, maybe settling on u32 instead of i32 in most places is better (fewer things to prove). Or maybe it doesn't matter much. For the start of the tutorial, i32 is important because the examples are all about overflow. But after that we could go either way. -->

In the following we will sometimes use unsigned integer types to focus on specifying memory ownership, rather than the conditions necessary to show absence of C arithmetic undefined behaviour.

### Exercises

_Swap._ Specify the function `swap`, which takes two RW `unsigned int` pointers and swaps their values.

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

## Ownership of compound objects

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
C supports strong updates in certain situations and so take _ = RW<ct>(p) in the requires clause could very well have a different C type than take _ = RW<ct2>(p) in the ensures clause.

The reason RW needs a C-type is so that it can (a) figure out the size of the sub-heap being claimed and (b) figure out how one may need to destructure the type (unions, struct fields and padding, arrays). The relationship is that for take x = RW<ct>(expr), expr : pointer, x : to_basetype(ct).

There is a design decision to consider here rems-project/cerberus#349
-->

### Compound RW and W resources

While one might like to think of a struct as a single (compound) object that is manipulated as a whole, C permits more flexible struct manipulation: given a struct pointer, programmers can construct pointers to _individual struct members_ and manipulate these as values, including even passing them to other functions.

CN therefore cannot treat resources for compound C types like structs as primitive, indivisible units. Instead, `RW<T>` and `W<T>` are defined inductively on the structure of the C-type `T`.

For struct types `T`, the `RW<T>` resource is defined as the collection of `RW` resources for its members (as well as `W` resources for any padding bytes in-between them). The resource `W<T>`, similarly, is made up of `W` resources for all members (and padding bytes).

To handle code that manipulates pointers into parts of a struct object, CN can automatically decompose a struct resource into the member resources, and it can recompose the struct later, as needed. The following example illustrates this.

Recall the function `zero` from our earlier exercise. It takes an `int` pointer to uninitialised memory, with `W<int>` ownership, and initialises the value to zero, returning an `RW<int>` resource with output `0`.

Now consider the function `init_point`, shown below, which takes a pointer `p` to a `struct point` and zero-initialises its members by calling `zero` twice, once with a pointer to struct member `x`, and once with a pointer to `y`.

```c title="exercises/init_point.c"
--8<--
exercises/init_point.c
--8<--
```

As stated in its precondition, `init_point` receives ownership `W<struct point>(p)`. The `zero` function, however, works on `int` pointers and requires `W<int>` ownership.

CN can prove the calls to `zero` with `&p->x` and `&p->y` are safe because it decomposes the `W<struct point>(p)` into a `W<int>` for member `x` and a `W<int>` for member `y`. Later, the reverse happens: following the two calls to `zero`, as per `zero`’s precondition, `init_point` has ownership of two adjacent `RW<int>` resources – ownership for the two struct member pointers, with the member now initialised. Since the postcondition of `init_point` requires ownership `RW<struct point>(p)`, CN combines these back into a compound resource. The resulting `RW<point struct>` resource has for an output the struct value `P_post` that is composed of the zeroed member values for `x` and `y`.

### Resource inference

To handle the required resource inference, CN "`eagerly`" decomposes all `struct` resources into resources for the struct members, and "`lazily`" re-composes them as needed.

We can see this if, for instance, we experimentally change the `transpose` example from above to force a type error. Let’s insert an `/*@ assert(false) @*/` CN assertion in the middle of the `transpose` function, so we can inspect CN’s proof context shown in the error report. (More on CN assertions later.)

<!-- TODO: BCP: Recheck that what we say here matches what it actually looks like -->

```c title="exercises/transpose.broken.c"
--8<--
exercises/transpose.broken.c
--8<--
```

The precondition of `transpose` asserts ownership of an `RW<struct point>(p)` resource. The error report now instead lists under "`Available resources`" two resources:

- `RW<signed int>(member_shift<point>(p, x))` with output `P.x` and

- `RW<signed int>(member_shift<point>(p, y))` with output `P.y`

<!-- TODO: BCP: We should verify that it really does say this. -->

Here `member_shift<s>(p,m)` is the CN expression that constructs, from a `struct s` pointer `p`, the "`shifted`" pointer for its member `m`.

When the function returns, the two member resources are recombined "`on demand`" to satisfy the postcondition `RW<struct point>(p)`.

### Exercises

_Init point._ Insert CN `assert(false)` statements in different statement positions of `init_point` and check how the available resources evolve.

_Transpose (again)._ Recreate the transpose function from before, now using the swap function verified earlier (for `struct upoint`, with unsigned member values).

BCP: FIX!!

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

## Arrays and loops

Another common datatype in C is arrays. Reasoning about memory ownership for arrays is more difficult than for the datatypes we have seen so far, for two reasons: (1) C allows the programmer to access arrays using _computed pointers_, and (2) the size of an array does not need to be known as a constant at compile time.

To support reasoning about code manipulating arrays and computed pointers, CN has _iterated resources_. For instance, to specify ownership of an `int` array with 10 cells starting at pointer `p`, CN uses the following iterated resource:

<!-- TODO: BCP: Another tricky naming / capitalization puzzle: The index of an "each" has CN type i32, so strictly speaking I believe it should be written with a capital "I". But insisting on this feels like insisting on a distinction that most CN programmers would never even notice, much less be confused by. I think this is another instance of the way C and CN integer types are partly but not completely squished together. -->

```c
each (i32 i; 0i32 <= i && i < 10i32)
{ RW<int>(array_shift<int>(p,i)) }
```

In detail, this can be read as follows:

- for each integer `i` of CN type `i32`, …

- if `i` is between `0` and `10`, …

- assert ownership of a resource `RW<int>` …

- for cell `i` of the array with base-address `p`.

Here `array_shift<int>(p,i)` computes a pointer into the array at pointer `p`, appropriately offset for index `i`.

In general, iterated resource specifications take the form

```c
each (BT Q; GUARD) { RESOURCE }
```

comprising three parts:

- `BT Q`, for some CN type `BT` and name `Q`, introduces the quantifier `Q` of basetype `BT`, which is bound in `GUARD` and `RESOURCE`;

- `GUARD` is a boolean-typed expression delimiting the instances of `Q` for which ownership is asserted; and

- `RESOURCE` is any non-iterated CN resource.

### First array example

Let’s see how this applies to a simple array-manipulating function. Function `read` takes three arguments: the base pointer `p` of an `int` array, the length `n` of the array, and an index `i` into the array; `read` then returns the value of the `i`-th array cell.

```c title="exercises/array_load.broken.c"
--8<--
exercises/array_load.broken.c
--8<--
```

The CN precondition requires

- ownership of the array on entry — one `RW<int>` resource for each array index between `0` and `n` — and
- that `i` lies within the range of RW indices.

On exit the array ownership is returned again.

This specification, in principle, should ensure that the access `p[i]` is safe. However, running CN on the example produces an error: CN is unable to find the required ownership for reading `p[i]`.

```
cn verify solutions/array_load.broken.c
[1/1]: read
build/solutions/array_load.broken.c:5:10: error: Missing resource for reading
return p[i];
^~~~
Resource needed: RW<signed int>(array_shift<signed int>(p, (u64)i))
```

The reason is that, when searching for a required resource, such as the `RW` resource for `p[i]` here, CN’s resource inference does not consider iterated resources. Quantifiers, as used by iterated resources, can make verification undecidable, so, in order to maintain predictable type checking, CN delegates this aspect of the reasoning to the user.

To make the `RW` resource required for accessing `p[i]` available to CN’s resource inference we have to explicitly "`focus`" ownership for index `i` out of the iterated resource.

```c title="exercises/array_load.c"
--8<--
exercises/array_load.c
--8<--
```

Here the CN comment `/*@ focus RW<int>, i; @*/` is a proof hint in the form of a "`ghost statement`" that instructs CN to instantiate any available iterated `RW<int>` resource for index `i`. In our example this operation splits the iterated resource into two:

```c
each(i32 j; 0i32 <= j && j < n) { RW<int>(array_shift<int>(p,j)) }
```

is split into

1. the instantiation of the iterated resource at `i`

```c
RW<int>(array_shift<int>(p,i))
```

2. the remainder of the iterated resource, the ownership for all indices except `i`

```c
  each(i32 j; 0i32 <= j && j < n && j != i)
  { RW<int>(array_shift<int>(p,j)) }
```

After this extraction step, CN can use the (former) extracted resource to justify the access `p[i]`. Note that an `focus` statement's second argument can be any arithmetic expression, not just a single identifier like in this example.

Following an `focus` statement, CN remembers the extracted index and can automatically "`reverse`" the extraction when needed: after type checking the access `p[i]` CN must ensure the function’s postcondition holds, which needs the full array ownership again (including the extracted index `i`); remembering the index `i`, CN then automatically merges resources (1) and (2) again to obtain the required full array ownership, and completes the verification of the function.

So far the specification only guarantees safe execution but does not
specify the behaviour of `read`. To address this, let’s return to
the iterated resources in the function specification. When we specify
`take A = each ...` here, what is `A`? In CN, the output of an
iterated resource is a _map_ from indices to resource outputs. In this
example, where index `j` has CN type `i32` and the iterated
resource is `RW<int>`, the output `A` is a map from `i32`
indices to `i32` values — CN type `map<i32,i32>`. If the type of
`j` was `i64` and the resource `RW<char>`, `A` would have
type `map<i64,u8>`.

We can use this to refine our specification with information about the functional behaviour of `read`.

```c title="exercises/array_load2.c"
--8<--
exercises/array_load2.c
--8<--
```

We specify that `read` does not change the array — the outputs of `RW`,
`A` and `A_post`, taken before and after running the function, are
the same — and that the value returned is `A[i]`.

### Exercises

_Array read two._ Specify and verify the following function, `array_read_two`, which takes the base pointer `p` of an `unsigned int` array, the array length `n`, and two indices `i` and `j`. Assuming `i` and `j` are different, it returns the sum of the values at these two indices.

<!-- TODO: BCP: When we get around to renaming files in the examples directory, we should call this one array_swap or something else beginning with "array". -->

```c title="exercises/add_two_array.c"
--8<--
exercises/add_two_array.c
--8<--
```

<!--
TODO: BCP: In this one I got quite tangled up in different kinds of integers, then got tangled up in (I think) putting the focus declarations in the wrong place. (I didn't save the not-working version, I'm afraid.)

TODO: Sainati: I think it would be useful to have a int array version of this exercise as a worked example; I am not sure, for example, how one would express bounds requirements on the contents of an array in CN, as you would need to do here to ensure that p[i] + p[j] doesn’t overflow if p's contents are signed ints
-->

_Swap array._ Specify and verify `swap_array`, which swaps the values of two cells of an `int` array. Assume again that `i` and `j` are different, and describe the effect of `swap_array` on the array value using the CN map update expression `a[i:v]`, which denotes the same map as `a`, except with index `i` updated to `v`.

```c title="exercises/swap_array.c"
--8<--
exercises/swap_array.c
--8<--
```

<!--
TODO: BCP: I wrote this, which seemed natural but did not work -- I still don't fully understand why. I think this section will need some more examples / exercises to be fully digestible, or perhaps this is just yet another symptom of my imperfecdt understanding of how the numeric stuff works.

    void swap_array (int *p, int n, int i, int j)
    /*@ requires take a1 = each(i32 k; 0i32 <= k && k < n) { RW<unsigned int>(array_shift<unsigned int>(p,k)) };
                 0i32 <= i && i < n;
                 0i32 <= j && j < n;
                 j != i;
                 take xi = RW<unsigned int>(array_shift(p,i));
                 take xj = RW<unsigned int>(array_shift(p,j))
        ensures take a2 = each(i32 k; 0i32 <= k && k < n) { RW<unsigned int>(array_shift<unsigned int>(p,k)) };
                a1[i:xj][j:xi] == a2
    @*/
    {
      focus RW<unsigned int>, i;
      focus RW<unsigned int>, j;
      int tmp = p[i];
      p[i] = p[j];
      p[j] = tmp;
    }

-->

### Loops

The array examples covered so far manipulate one or two individual cells of an array. Another typical pattern in code working over arrays is to _loop_, uniformly accessing all cells of an array or a sub-range of it.

In order to verify code with loops, CN requires the user to supply loop invariants -- CN specifications of all RW resources and the constraints required to verify each iteration of the loop.

Let's take a look at a simple first example. The following function, `init_array`, takes the base pointer `p` of a `char` array and the array length `n` and writes `0` to each array cell.

<!-- TODO: BCP: Rename to array_init.c -->

```c title="exercises/init_array.c"
--8<--
exercises/init_array.c
--8<--
```

If, for the moment, we focus just on proving safe execution of `init_array`, ignoring its functional behaviour, a specification might look as above: on entry, `init_array` takes ownership of an iterated `RW<char>` resource -- one `RW` resource for each index `i` of type `u32` (so necessarily greater or equal to `0`) up to `n`; on exit `init_array` returns the ownership.

To verify this, we have to supply a loop invariant that specifies all resource ownership and the necessary constraints that hold before and after each iteration of the loop. Loop invariants are specified using the keyword `inv`, followed by CN specifications using the same syntax as in function pre- and postconditions. The variables in scope for loop invariants are all in-scope C variables, as well as CN variables introduced in the function precondition. _In loop invariants, the name of a C variable refers to its current value_ (more on this shortly).

```c title="solutions/init_array.c"
--8<--
solutions/init_array.c
--8<--
```

<!--
TODO: BCP: Concrete syntax: Why not write something like "unchanged {p,n}" or "unchanged: p,n"?
-->

The main condition here is unsurprising: we specify ownership of an iterated resource for an array just like in the the pre- and postcondition.

The second thing we need to do, however, is less straightforward. Recall that, as discussed at the start of the tutorial, function arguments in C are mutable. Although, in this example, it is obvious that `p` and `n` do not change, CN currently requires the loop invariant to explicitly state this, using special notation `{p} unchanged` (and similarly for `n`).

**Note.** If we forget to specify `unchanged`, this can lead to confusing errors. In this example, for instance, CN would verify the loop against the loop invariant, but would be unable to prove a function postcondition seemingly directly implied by the loop invariant (lacking the information that the postcondition's `p` and `n` are the same as the loop invariant's). Future CN versions may handle loop invariants differently and treat variables as immutable by default.

<!--
TODO: BCP: This seems like a good idea!
-->

The final piece needed in the verification is an `focus` statement, as used in the previous examples: to separate the individual `RW<char>` resource for index `j` out of the iterated `RW` resource and make it available to the resource inference, we specify `focus RW<char>, j;`.

With the `inv` and `focus` statements in place, CN accepts the function.

### Second loop example

The specification of `init_array` is overly strong: it requires an iterated `RW` resource for the array on entry. If, as the name suggests, the purpose of `init_array` is to initialise the array, then a precondition asserting only an iterated `W` resource for the array should also be sufficient. The modified specification is then as follows.

```c title="exercises/init_array2.c"
--8<--
exercises/init_array2.c
--8<--
```

This specification _should_ hold: assuming ownership of an uninitialised array on entry, each iteration of the loop initialises one cell of the array, moving it from `W` to `RW` "`state`", so that on function return the full array is initialised. (Recall that stores only require `W` ownership of the written memory location, i.e., ownership of not-necessarily-initialised memory.)

To verify this modified example we again need a loop Invariant. But
this time the loop invariant is more involved: since each iteration of
the loop initialises one more array cell, the loop invariant has to do
precise book-keeping of the initialisation status of the different
sections of the array.

To do this, we partition the array ownership into two parts: for each index of the array the loop has already visited, we have an `RW` resource, for all other array indices we have the (unchanged) `W` ownership.

```c title="solutions/init_array2.c"
--8<--
solutions/init_array2.c
--8<--
```

Let's go through this line-by-line:

- We assert ownership of an iterated `RW` resource, one for each index `i` strictly smaller than loop variable `j`.

- All remaining indices `i`, between `j` and `n` are still uninitialised, so part of the iterated `W` resource.

- As in the previous example, we assert `p` and `n` are unchanged.

- Finally, unlike in the previous example, this loop invariant involves `j`. We therefore also need to know that `j` does not exceed the array length `n`. Otherwise CN would not be able to prove that, on completing the last loop iteration, `j=n` holds. This, in turn, is needed to show that, when the function returns, ownership of the iterated `RW` resource --- as specified in the loop invariant --- is fully consumed by the function's post-condition and there is no left-over unused resource.

As before, we also have to instruct CN to `focus` ownership of individual array cells out of the iterated resources:

- to allow CN to focus the individual `W` to be written, we use `focus W<char>, j;`;

- the store returns a matching `RW<char>` resource for index `j`;

- finally, we add `focus RW<char>, j;` to allow CN to "`attach`" this resource to the iterated `RW` resource. CN issues a warning, because nothing is, in fact, extracted: we are using `focus` only for the "`reverse`" direction.

<!-- TODO: BCP: That last bit is mysterious. -->
<!-- Dhruv: See long explanation and issue here: rems-project/cerberus#498 -->

### Exercises

**Init array reverse.** Verify the function `init_array_rev`, which has the same specification as `init_array2`, but initializes the array in decreasing index order (from right to left).

```c title="exercises/init_array_rev.c"
--8<--
exercises/init_array_rev.c
--8<--
```

<!-- TODO: BCP: The transition to the next section is awkward. Needs a sentence or two to signal that we're changing topics. Some better visual indication would also be nice. -->

<!--

---

---

---

---

---

TODO: BCP: I'll put my new stuff below here...
-->

## Defining Predicates

<!-- We should show how to define predicates earlier -- -->
<!-- - e.g., with numeric ranges!! -->

<!--
TODO: BCP: The text becomes a bit sketchy from here on! But hopefully there's
still enough structure here to make sense of the examples...
-->

Suppose we want to write a function that takes _two_ pointers to
integers and increments the contents of both of them.

First, let's deal with the "normal" case where the two arguments do
not alias...

```c title="exercises/slf_incr2_noalias.c"
--8<--
exercises/slf_incr2_noalias.c
--8<--
```

But what if they do alias? The clunky solution is to write a whole
different version of `incr2` with a different embedded specification...

```c title="exercises/slf_incr2_alias.c"
--8<--
exercises/slf_incr2_alias.c
--8<--
```

This version does correctly state that the final values of `p` and `q` are,m respectively, `3` and `1` more than their original values. But the way we got there -- by duplicating the whole function `incr2`, is horrible.

<!-- TODO: Sainati: I think it would be useful here to add an explanation for how CN's type checking works. -->
<!-- For example, in the definition of BothOwned here, how is CN able to prove that `take pv = RW<unsigned int>(p);` -->
<!-- type checks, since all we know about `p` in the definition of the predicate is that it's a pointer? -->

A better way is to define a _predicate_ that captures both the aliased
and the non-aliased cases together and use it in the pre- and
postconditions:

<!-- TODO: Sainati: I think it would be useful here to add an explanation for how CN's type checking works. -->
<!-- For example, in the definition of BothOwned here, how is CN able to prove that `take pv = RW<unsigned int>(p);` -->
<!-- type checks, since all we know about `p` in the definition of the predicate is that it's a pointer? -->

```c title="exercises/slf_incr2.c"
--8<--
exercises/slf_incr2.c
--8<--
```

<!-- TODO: BCP: "BothOwned" is a pretty awkward name. -->
<!-- TODO: BCP: We haven't introduced CN records. In particular, C programmers may be surprised that we don't have to pre-declare record types. -->
<!-- TODO: BCP: the annotation on incr2 needs some unpacking for readers!! -->
<!-- TODO: BCP: first use of the "split_case" annotation -->

## Allocating and Deallocating Memory

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

## Lists

<!-- TODO: BCP: Better intro needed -->

Now it's time to look at some more interesting heap structures.

To begin with, here is a C definition for linked list cells, together
with allocation and deallocation functions:

<!-- TODO: BCP: Here and in several other places, we should use the "take \_ = ..." syntax when the RW value is not used. And we should explain it the first time we use it. -->

```c title="exercises/list/c_types.h"
--8<--
exercises/list/c_types.h
--8<--
```

<!-- TODO: BCP: Per discussion with Christopher, Cassia, and Daniel, the word "predicate" is quite confusing for newcomers (in logic, predicates do not return things!). A more neutral word might make for significantly easier onboarding. -->
<!-- Dhruv: Or no keyword? rems-project/cerberus#304 How about traversal? -->
<!-- BCP: No keyword sounds even better. But "traversal" in the interim is not bad. Or maybe "extractor" or something like that? -->

To write specifications for C functions that manipulate lists, we need
to define a CN "predicate" that describes specification-level list
structures, as one would do in ML, Haskell, or Coq. We use the
datatype `List` for CN-level lists.

Intuitively, the `SLList_At` predicate walks over a singly-linked
pointer structure in the C heap and extracts an `RW` version of
the CN-level list that it represents.

```c title="exercises/list/cn_types.h"
--8<--
exercises/list/cn_types.h
--8<--
```

We can also write _functions_ on CN-level lists by ordinary functional
programming (in a slightly strange, unholy-union-of-C-and-Rust
syntax):

```c title="exercises/list/hdtl.h"
--8<--
exercises/list/hdtl.h
--8<--
```

We use the `SLList_At` predicate to specify functions returning the
empty list and the cons of a number and a list.

```c title="exercises/list/constructors.h"
--8<--
exercises/list/constructors.h
--8<--
```

Finally, we can collect all this stuff into a single header file. (We
add the usual C `#ifndef` gorp to avoid complaints from the compiler
if it happens to get included twice from the same source file later.)

```c title="exercises/list/headers.verif.h"
--8<--
exercises/list/headers.verif.h
--8<--
```

<!--
TODO: BCP: The 'return != NULL' should not be needed, but to remove it
we need to change the callers of all the allocation functions to check
for NULL and exit (which requires adding a spec for exit).
-->

### Append

With this basic infrastructure in place, we can start specifying and
verifying list-manipulating functions. First, `append`.

Here is its specification (in a separate file, because we'll want to
use it multiple times below.)

```c title="exercises/list/append.h"
--8<--
exercises/list/append.h
--8<--
```

Here is a simple destructive `append` function. Note the two uses
of the `unfold` annotation in the body, which are needed to help the
CN typechecker. The `unfold` annotation is an instruction to CN to replace a call to a recursive (CN) function (in this case `append`)
with its definition, and is necessary because CN is unable to automatically determine when and where to expand recursive definitions on its own.

<!-- TODO: BCP: Can someone add a more technical explanation of why they are needed and exactly what they do? -->

```c title="exercises/list/append.c"
--8<--
exercises/list/append.c
--8<--
```

### List copy

Here is an allocating list copy function with a pleasantly light
annotation burden.

```c title="exercises/list/copy.c"
--8<--
exercises/list/copy.c
--8<--
```

### Merge sort

<!-- TODO: BCP: This could use a gentler explanation (probably in pieces) -->

Finally, here is a slightly tricky in-place version of merge sort that
avoids allocating any new list cells in the splitting step by taking
alternate cells from the original list and linking them together into
two new lists of roughly equal lengths.

<!-- TODO: BCP: We've heard from more than one reader that this example is particularly hard to digest without some additional help -->

<!-- TODO: BCP: Nit: Merge multiple requires and ensures clauses into one -->

```c title="exercises/list/mergesort.c"
--8<--
exercises/list/mergesort.c
--8<--
```

### Exercises

_Allocating append_. Fill in the CN annotations on
`IntList_append2`. (You will need some in the body as well as at
the top.)

```c title="exercises/list/append2.c"
--8<--
exercises/list/append2.c
--8<--
```

Note that it would not make sense to do the usual
functional-programming trick of copying xs but sharing ys. (Why?)

_Length_. Add annotations as appropriate:

```c title="exercises/list/length.c"
--8<--
exercises/list/length.c
--8<--
```

_List deallocation_. Fill in the body of the following procedure and
add annotations as appropriate:

```c title="exercises/list/free.c"
--8<--
exercises/list/free.c
--8<--
```

_Length with an accumulator_. Add annotations as appropriate:

<!-- TODO: BCP: Removing / forgetting the unfold in this one gives a truly -->
<!-- bizarre error message saying that the constraint "n == (n + length(L1))" -->
<!-- is unsatisfiable... -->

<!-- TODO: Sainati: when I went through the tutorial, the file provided for this exercise was already "complete" in that -->
<!-- it already had all the necessary annotations present for CN to verify it -->

```c title="exercises/slf_length_acc.c"
--8<--
exercises/slf_length_acc.c
--8<--
```

## Working with External Lemmas

<!-- TODO: BCP: This section should also show what the proof of the lemmas -->

looks like on the Coq side!

<!-- TODO: BCP: This needs to be filled in urgently!! -->
<!-- Dhruyv: There are some examples in the Cerberus repo tests? rems-project/cerberus@20d9d5c -->

<!--
TODO: BCP:
think about capitalization, etc., for lemma names
push_lemma should be Push_lemma, I guess? Or lemma_push?
snoc_facts should be lemma_Snoc or something
others?
-->

### List reverse

The specification of list reversal in CN relies on the familiar
recursive list reverse function, with a recursive helper.

```c title="exercises/list/snoc.h"
--8<--
exercises/list/snoc.h
--8<--
```

```c title="exercises/list/rev.h"
--8<--
exercises/list/rev.h
--8<--
```

To reason about the C implementation of list reverse, we need to help
the SMT solver by enriching its knowledge base with a couple of facts
about lists. The proofs of these facts require induction, so in CN we
simply state them as lemmas and defer the proofs to Coq.

```c title="exercises/list/rev_lemmas.h"
--8<--
exercises/list/rev_lemmas.h
--8<--
```

Having stated these lemmas, we can now complete the specification and
proof of `IntList_rev`. Note the two places where `apply` is used
to tell the SMT solver where to pay attention to the lemmas.

<!--
TODO: BCP: Why can't it always pay attention to them? (I guess
"performance", but at least it would be nice to be able to declare a
general scope where a given set of lemmas might be needed, rather than
specifying exactly where to use them.)
-->

```c title="exercises/list/rev.c"
--8<--
exercises/list/rev.c
--8<--
```

For comparison, here is another way to write the program, using a
while loop instead of recursion, with its specification and proof.

<!-- TODO: BCP: Why 0 instead of NULL?? (Is 0 better?) -->

```c title="exercises/list/rev_alt.c"
--8<--
exercises/list/rev_alt.c
--8<--
```

### Exercises

**Sized stacks:** Fill in annotations where requested:

<!-- TODO: BCP: type_synonym has not been introduced yet -->

```c title="exercises/slf_sized_stack.c"
--8<--
exercises/slf_sized_stack.c
--8<--
```

<!-- ====================================================================== -->

<!--

## More on CN Annotations

_TODO_:

- Introduce all the different sorts of CN annotations (e.g.,
  `split_case`) individually with small examples and exercises.
-->

<!-- ====================================================================== -->

## CN Style

<!-- TODO: BCP: If we are agreed on the naming conventions suggested in /NAMING-CONVENTIONS.md, we could move that material here. -->

This section gathers some advice on stylistic conventions and best
practices in CN.

### Constants

The syntax of the C language does not actually include constants.
Instead, the convention is to use the macro preprocessor to replace
symbolic names by their definitions before the C compiler ever sees
them.

This raises a slight awkwardness in CN, because CN specifications and
annotations are written in C comments, so they are not transformed by
the preprocessor. However, we can approximate the effect of constant
_values_ by defining constant _functions_. We've been working with
some of these already, e.g., `MINi32()`, but it is also possible to
define our own constant functions. Here is the officially approved
idiom:

```c title="exercises/const_example.c"
--8<--
exercises/const_example.c
--8<--
```

Here's how it works:

- We first define a C macro `CONST` in the usual way.

- The next two lines "import" this constant into CN by defining a CN
  function `CONST()` whose body is the C function `c_CONST()`. The
  body of `c_CONST` returns the value of the macro `CONST`. Notice
  that the declaration of `CONST()` has no body.

- The annotation `/*@ cn_function CONST; @*/` links
  the two functions, `CONST()` and `cn_CONST()`.

Of course, we could achieve the same effect by defining the CN
function `CONST()` directly...

```c title="exercises/const_example_lessgood.c"
--8<--
exercises/const_example_lessgood.c
--8<--
```

...but this version repeats the number `1` in two places -- a
potential source of nasty bugs!

<!-- ====================================================================== -->
<!-- ====================================================================== -->
<!-- ====================================================================== -->

## Case Studies

To close out the tutorial, let's look at some larger examples.

### Case Study: Imperative Queues

A queue is a linked list with O(1) operations for adding things to one
end (the "back") and removing them from the other (the "front"). Here
are the C type definitions:

```c title="exercises/queue/c_types.h"
--8<--
exercises/queue/c_types.h
--8<--
```

A queue consists of a pair of pointers, one pointing to the front
element, which is the first in a linked list of `queue_cell`s,
the other pointing directly to the last cell in this list. If the
queue is empty, both pointers are NULL.

Abstractly, a queue just represents a list, so we can reuse the `List`
type from the list examples earlier in the tutorial.

```c title="exercises/queue/cn_types_1.h"
--8<--
exercises/queue/cn_types_1.h
--8<--
```

Given a pointer to a `queue` struct, this predicate grabs ownership
of the struct, asserts that the `front` and `back` pointers must
either both be NULL or both be non-NULL, and then hands off to an
auxiliary predicate `QueueFB`. Note that `QueuePtr_At` returns a
`List` -- that is, the abstract view of a queue heap structure is
simply the sequence of elements that it contains. The difference
between a queue and a singly or doubly linked list is simply one of
concrete representation.

`QueueFB` is where the interesting part starts. (Conceptually,
`QueueFB` is part of `QueuePTR`, but CN currently allows
conditional expressions only at the beginning of predicate
definitions, not after a `take`, so we need to make a separate
auxiliary predicate.)

```c title="exercises/queue/cn_types_2.h"
--8<--
exercises/queue/cn_types_2.h
--8<--
```

First, we case on whether the `front` of the queue is NULL. If so,
then the queue is empty and we return the empty sequence.

If the queue is not empty, we need to walk down the linked list of
elements and gather up all their values into a sequence. But we must
treat the last element of the queue specially, for two reasons.
First, since the `push` operation is going to follow the `back`
pointer directly to the last list cell without traversing all the
others, we need to `take` that element now rather than waiting to
get to it at the end of the recursion starting from the `front`.
Second, and relatedly, there will be two pointers to this final list
cell -- one from the `back` field and one from the `next` field of
the second to last cell (or the `front` pointer, if there is only
one cell in the list), so we need to be careful not to `take` this
cell twice.

Accordingly, we begin by `take`-ing the tail cell and passing it
separately to the `QueueAux` predicate, which has the job of
walking down the cells from the front and gathering all the rest of
them into a sequence. We take the result from `QueueAux` and
`snoc` on the very last element.

The `assert (is_null(B.next))` here gives the CN verifier a crucial
piece of information about an invariant of the representation: The
`back` pointer always points to the very last cell in the list, so
its `next` field will always be NULL.

<!-- TODO: BCP: How to help people guess that this is needed?? -->

Finally, the `QueueAux` predicate recurses down the list of
cells and returns a list of their contents.

```c title="exercises/queue/cn_types_3.h"
--8<--
exercises/queue/cn_types_3.h
--8<--
```

Its first argument (`f`) starts out at `front` and progresses
through the queue on recursive calls; its `b` argument is always a
pointer to the very last cell.

When `f` and `b` are equal, we have reached the last cell and
there is nothing to do. We don't even have to build a singleton
list: that's going to happen one level up, in `QueueFB`.

Otherwise, we `take` the fields of the `f`, make a recurive
call to `QueueAux` to process the rest of the cells, and cons the
`first` field of this cell onto the resulting sequence before
returning it. Again, we need to help the CN verifier by explicitly
informing it of the invariant that we know, that `C.next` cannot be
null if `f` and `b` are different.

Now we need a bit of boilerplate: just as with linked lists, we need
to be able to allocate and deallocate queues and queue cells. There
are no interesting novelties here.

```c title="exercises/queue/allocation.verif.h"
--8<--
exercises/queue/allocation.verif.h
--8<--
```

<!-- ====================================================================== -->

_Exercise_: The function for creating an empty queue just needs to set
both of its fields to NULL. See if you can fill in its specification.

```c title="exercises/queue/empty.c"
--8<--
exercises/queue/empty.c
--8<--
```

<!-- ====================================================================== -->

The push and pop operations are more involved. Let's look at `push`
first.

Here's the unannotated C code -- make sure you understand it.

```c title="exercises/queue/push_orig.broken.c"
--8<--
exercises/queue/push_orig.broken.c
--8<--
```

_Exercise_: Before reading on, see if you can write down a reasonable
top-level specification for this operation.

One thing you might find odd about this code is that there's a
`return` statement at the end of each branch of the conditional,
rather than a single `return` at the bottom. The reason for this is
that, when CN analyzes a function body containing a conditional, it
effectively _copies_ all the code after the conditional into each of
the branches. Then, if verification encounters an error related to
this code -- e.g., "you didn't establish the `ensures` conditions at
the point of returning -- the error message will be confusing because
it will not be clear which branch of the conditional it is associated
with.

Now, here is the annotated version of the `push` operation.

```c title="exercises/queue/push.c"
--8<--
exercises/queue/push.c
--8<--
```

The case where the queue starts out empty (`q->back == 0`) is easy.
CN can work it out all by itself.

The case where the starting queue is nonempty is more interesting.
The `push` operation messes with the end of the sequence of queue
elements, so we should expect that validating `push` is going to
require some reasoning about this sequence. Here, in fact, is the
lemma we need.

<!-- TODO: BCP: Not sure I can explain what "pointer" means here, or why we don't need to declare more specific types for these arguments to the lemma. -->
<!-- Dhruv: See above comments about strong updates: in a requires/ensures, the types are given by the arguments in scope, but here we don't have that. -->

```c title="exercises/queue/push_lemma.h"
--8<--
exercises/queue/push_lemma.h
--8<--
```

This says, in effect, that we have two choices for how to read out the
values in some chain of queue cells of length at least 2, starting
with the cell `front` and terminating when we get to the next cell
_following_ some given cell `p` -- call it `c`. We can either
gather up all the cells from `front` to `c`, or we can gather up
just the cells from `front` to `p` and then `snoc` on the single
value from `c`.

When we apply this lemma, `p` will be the old `back` cell and
`c` will be the new one. But to prove it (by induction, of course),
we need to state it more generally, allowing `p` to be any internal
cell in the list starting at `front` and `c` its successor.

The reason we need this lemma is that, to add a new cell at the end of
the queue, we need to reassign ownership of the old `back` cell.
In the precondition of `push`, we took ownership of this cell
separately from the rest; in the postcondition, it needs to be treated
as part of the rest (so that the new `back` cell can now be treated
specially).

One interesting technicality is worth noting: After the assignment
`q->back = c`, we can no longer prove `QueueFB(q->front,
oldback)`, but we don't care about this, since we want to prove
`QueueFB(q->front, q->back)`. However, crucially,
`QueueAux(q->front, oldback)` is still true.

<!-- ====================================================================== -->

Now let's look at the `pop` operation. Here is the un-annotated
version:

```c title="exercises/queue/pop_orig.broken.c"
--8<--
exercises/queue/pop_orig.broken.c
--8<--
```

_Exercise_: Again, before reading on, see if you can write down a
plausible top-level specification. (For extra credit, see how far you
can get with verifying it!)

Here is the fully annotated `pop` code:

```c title="exercises/queue/pop.c"
--8<--
exercises/queue/pop.c
--8<--
```

There are three annotations to explain. Let's consider them in order.

First, the `split_case` on `is_null(q->front)` is needed to tell
CN which of the branches of the `if` at the beginning of the
`QueueFB` predicate it can "unpack". (`QueuePtr_At` can be
unpacked immediately because it is unconditional, but `QueueFB`
cannot.)

<!-- TODO: BCP: the word "unpack" is mysterious here. -->

The guard/condition for `QueueFB` is `is_null(front)`, which is
why we need to do a `split_case` on this value. On one branch of the
`split_case` we have a contradiction: the fact that `before ==
Nil{}` (from `QueueFB`) conflicts with `before != Nil`
from the precondition, so that case is immediate. On the other
branch, CN now knows that the queue is non-empty, as required, and type
checking proceeds.

When `h == q->back`, we are in the case where the queue contains
just a single element, so we just need to NULL out its `front` and
`back` fields and deallocate the dead cell. The `unfold`
annotation is needed because the `snoc` function is recursive, so CN
doesn't do the unfolding automatically.

Finally, when the queue contains two or more elements, we need to
deallocate the front cell, return its `first` field, and redirect
the `front` field of the queue structure to point to the next cell.
To push the verification through, we need a simple lemma about the
`snoc` function:

```c title="exercises/queue/pop_lemma.h"
--8<--
exercises/queue/pop_lemma.h
--8<--
```

The crucial part of this lemma is the last three lines, which express
a simple, general fact about `snoc`:
if we form a sequence by calling `snoc` to add a final element
`B.first` to a sequence with head element `x` and tail `Q`, then the
head of the resulting sequence is still `x`, and its tail is `snoc
(Q, B.first)`.

The `requires` clause and the first three lines of the `ensures`
clause simply set things up so that we can name the various values we
are talking about. Since these values come from structures in the
heap, we need to take ownership of them. And since lemmas in CN are
effectively just trusted functions that can also take in ghost values,
we need to take ownership in both the `requires` and `ensures`
clauses. (Taking them just in the `requires` clause would imply
that they are consumed and deallocated when the lemma is applied --
not what we want!)

<!-- TODO: BCP: The thing about ghost values is mysterious. -->
<!-- How to say it better? -->

(The only reason we can't currently prove this lemma in CN is that we
don't have `take`s in CN statements, because this is just a simple
unfolding.)

<!-- TODO: BCP: Ugh. -->

_Exercise_:
Investigate what happens when you make each of the following changes
to the queue definitions. What error does CN report? Where are the
telltale clues in the error report that suggest what the problem was?

- Remove `assert (is_null(B.next));` from `InqQueueFB`.
- Remove `assert (is_null(B.next));` from `InqQueueAux`.
- Remove one or both of occurrences of `free_queue_cell(f)` in
  `pop_queue`.
- Remove, in turn, each of the CN annotations in the bodies of
  `pop_queue` and `push_queue`.

_Exercise_: The conditional in the `pop` function tests whether or
not `f == b` to find out whether we have reached the last element of
the queue. Another way to get the same information would be to test
whether `f->next == 0`. Can you verify this version?
_Note_: I (BCP) have not worked out the details, so am not sure how hard
this is (or if it is even not possible, though I'd be surprised).
Please let me know if you get it working!

_Exercise_: Looking at the code for the `pop` operation,
it might seem reasonable to move the identical assignments to `x` in both
branches to above the `if`. This doesn't "just work" because the
ownership reasoning is different. In the first case, ownership of
`h` comes from `QueueFB` (because `h == q->back`). In the
second case, it comes from `QueueAux` (because `h !=
q->back`).

Can you generalize the `snoc_facts` lemma to handle both cases? You
can get past the dereference with a `split_case` but formulating the
lemma before the `return` will be a bit more complicated.

<!-- -->

_Note_: Again, this has not been shown to be possible, but Dhruv
believes it should be!

<!-- ====================================================================== -->
<!-- ====================================================================== -->
<!-- ====================================================================== -->

### Case Study: Doubly Linked Lists

<!-- TODO: BCP: The rest of the tutorial (from here to the end) needs to be checked for consistency of naming and capitalization conventions. -->

A doubly linked list is a linked list where each node has a pointer
to both the next node and the previous node. This allows for O(1)
operations for adding or removing nodes anywhere in the list.

Because of all the sharing in this data structure, the separation
reasoning is a bit tricky. We'll give you the core definitions and
then invite you to help fill in the annotations for some of the
functions that manipulate doubly linked lists.

First, here is the C type definition:

```c title="exercises/dll/c_types.h"
--8<--
exercises/dll/c_types.h
--8<--
```

The idea behind the representation of this list is that we don't keep
track of the front or back, but rather we take any node in the list
and have a sequence to the left and to the right of that node. The `left`
and `right` are from the point of view of the node itself, so `left`
is kept in reverse order. Additionally, similarly to in the
`Imperative Queues` example, we can reuse the `List` type.

```c title="exercises/dll/cn_types.h"
--8<--
exercises/dll/cn_types.h
--8<--
```

The predicate for this datatype is a bit complicated. The idea is that
we first own the node that is passed in. Then we follow all of the
`prev` pointers to own everything backwards from the node, and finally
all the `next` pointers to own everything forwards from the node, to
construct the `left` and `right` fields.

<!-- TODO: BCP: Maybe rethink the Own_Forwards / Backwards naming -- would something like Queue_At_Left and Queue_At_Right be clearer?? -->

```c title="exercises/dll/predicates.h"
--8<--
exercises/dll/predicates.h
--8<--
```

Note that `Dll_at` takes ownership of the node passed in, and then
calls `Own_Backwards` and `Own_Forwards`, which recursively take
ownership of the rest of the list.

Also, notice that `Own_Forwards` and `Own_Backwards` include `ptr_eq`
assertions for the `prev` and `next` pointers. This is to ensure that
the nodes in the list are correctly doubly linked. For example, the
line `assert (ptr_eq(n.prev, prev_pointer));` in `Own_Forwards`
ensures that the current node correctly points backward to the
previous node in the list. The line `assert(ptr_eq(prev_node.next,
p));` ensures that the previous node correctly points forward to the
current node.

Before we move on to the functions that manipulate doubly linked
lists, we need to define a few "getter" functions that will allow us
to access the fields of our `Dll` datatype. This will make the
specifications easier to write.

```c title="exercises/dll/getters.h"
--8<--
exercises/dll/getters.h
--8<--
```

We also need some boilerplate for allocation and deallocation.

```c title="exercises/dll/malloc_free.h"
--8<--
exercises/dll/malloc_free.h
--8<--
```

For convenience, we gather all of these files into a single header file.

```c title="exercises/dll/headers.verif.h"
--8<--
exercises/dll/headers.verif.h
--8<--
```

<!-- ====================================================================== -->

Now we can move on to an initialization function. Since an empty list
is represented as a null pointer, we will look at initializing a
singleton list (or in other words, a list with only one item).

```c title="exercises/dll/singleton.c"
--8<--
exercises/dll/singleton.c
--8<--
```

<!-- ====================================================================== -->

The `add` and `remove` functions are where it gets a little tricker.
Let's start with `add`. Here is the unannotated version:

```c title="exercises/dll/add_orig.broken.c"
--8<--
exercises/dll/add_orig.broken.c
--8<--
```

_Exercise_: Before reading on, see if you can figure out what
specification is appropriate and what other are needed.

<!-- TODO: BCP: I rather doubt they are going to be able to come up with this specification on their own! We need to set it up earlier with a simpler example (maybe in a whoile earlier section) showing how to use conditionals in specs. -->

Now, here is the annotated version of the `add` operation:

```c title="exercises/dll/add.c"
--8<--
exercises/dll/add.c
--8<--
```

First, let's look at the pre- and post-conditions. The `requires`
clause is straightforward. We need to own the list centered around
the node that `n` points to. `Before` is a `Dll`
that is either empty, or it has a List to the left,
the current node that `n` points to, and a List to the right.
This corresponds to the state of the list when it is passed in.

In the ensures clause, we again establish ownership of the list, but
this time it is centered around the added node. This means that
`After` is a `Dll` structure similar to `Before`, except that the node
`curr` is now the created node. The old `curr` is pushed into the left
part of the new list. The conditional operator in the `ensures` clause
is saying that if the list was empty coming in, it now is a singleton
list. Otherwise, the left left part of the list now has the data from
the old `curr` node, the new `curr` node is the added node, and the
right part of the list is the same as before.

Now, let's look at the annotations in the function body. CN can
figure out the empty list case for itself, but it needs some help with
the non-empty list case. The `split_case` on `is_null(n->prev)`
tells CN to unpack the `Own_Backwards` predicate. Without this
annotation, CN cannot reason that we didn't lose the left half of the
list before we return, and will claim we are missing a resource for
returning. The `split_case` on `is_null(n->next->next)` is similar,
but for unpacking the `Own_Forwards` predicate. Note that we have to
go one more node forward to make sure that everything past `n->next`
is still RW at the end of the function.

Now let's look at the `remove` operation. Traditionally, a `remove`
operation for a list returns the integer that was removed. However we
also want all of our functions to return a pointer to the
list. Because of this, we define a `struct` that includes an `int`
and a `node`.

```c title="exercises/dll/dllist_and_int.h"
--8<--
exercises/dll/dllist_and_int.h
--8<--
```

Now we can look at the code for the `remove` operation. Here is the un-annotated version:

```c title="exercises/dll/remove_orig.broken.c"
--8<--
exercises/dll/remove_orig.broken.c
--8<--
```

_Exercise_: Before reading on, see if you can figure out what
specification is appropriate and what annotations are needed.

<!-- TODO: BCP: Again, unlikely the reader is going to be able to figure this out without help. We need some hints. -->

Now, here is the fully annotated version of the `remove` operation:

```c title="exercises/dll/remove.c"
--8<--
exercises/dll/remove.c
--8<--
```

First, let's look at the pre- and post-conditions. The `requires` clause says that we cannot remove a node from an empty list, so the pointer passed in must not be null. Then we take ownership of the list, and we
assign the node of that list to the identifier `del`
to make our spec more readable. So `Before` refers to the `Dll` when the function is called, and `del` refers to the node that will be deleted.

Then in the `ensures` clause, we must take ownership
of the `node_and_int` struct as well as the `Dll` that
the node is part of. Here, `After` refers to the `Dll`
when the function returns. We ensure that the int that is returned is the value of the deleted node, as intended. Then we have a complicated nested ternary conditional that ensures that `After` is the same as `Before` except for the deleted node. Let's break down this conditional:

- The first guard asks if both `del.prev` and `del.next` are null. In this case, we are removing the only node in the list, so the resulting list will be empty. The `else` branch of this conditional contains its own conditional.

- For the following conditional, the guard checks if 'del.prev' is
  _not_ null. This means that the returned node is `del.next`,
  regardless of whether or not `del.prev` is null. If this is the
  case, `After` is now centered around `del.next`, and the left part
  of the list is the same as before. Since `del.next` was previously
  the head of the right side, the right side loses its head in
  `After`. This is where we get `After == Dll{left:
Left_Sublist(Before), curr: Node(After), right: Tl(Right(Before))}`.

- The final `else` branch is the case where `del.next` is null, but
  `del.prev` is not null. In this case, the returned node is
  `del.prev`. This branch follows the same logic as the one before it,
  except now we are taking the head of the left side rather than the
  right side. Now the right side is unchanged, and the left side is just
  the tail, as seen shown in `After == Dll{left:
Tl(Left_Sublist(Before)), curr: Node(After), right: Right(Before)};`

The annotations in the function body are similar to in the `add`
function. Both of these `split_case` annotations are needed to unpack
the `Own_Forwards` and `Own_Backwards` predicates. Without them, CN
will not be able to reason that we didn't lose the left or right half
of the list before we return and will claim we are missing a resource
for returning.

<!-- ====================================================================== -->

_Exercise_: There are many other functions that one might want to
implement for a doubly linked list. For example, one might want to
implement a function that appends one list to another, or a function
that reverses a list. Try implementing a few of these functions and
writing their specifications.

_Exercise_: For extra practice, try coming up with one or two
variations on the Dll data structure itself (there are many!).

<!-- ====================================================================== -->
<!-- ====================================================================== -->
<!-- ====================================================================== -->

### Case Study: Airport Simulation

<!-- TODO: BCP: I'm nervous about this case study -- it is not nearly as well debugged as the others, and it seems potentially quite confusing. I propose deleting it, but if other like it we can try to whip it into better shape... -->

Suppose we have been tasked with writing a program that simulates a
runway at an airport. This airport is very small, so it only has one
runway, which is used for both takeoffs and landings. We want to
verify that the runway is always used safely, by checking the
following informal specification:

1. The runway has two modes: departure mode and arrival mode. The two
modes can never be active at the same time. Neither mode is active
at the beginning of the day.
<!-- TODO: BCP: Would it be simpler to say it is in arrival mode at the beginning of the day? What difference would that make? (Saying there are two modes and then immediately introducing a third one is a bit confusing.) -->

2. At any given moment, there is a waiting list of planes that need to
   land at the airport and planes that need to leave the
   airport. These are modeled with counters `W_A` for the number of
   planes waiting to arrive, and `W_D` for the number of planes
   waiting to depart.

3. At any moment, a plane is either waiting to arrive, waiting to
   depart, or on the runway. Once a plane has started arriving or
   departing, the corresponding counter (`W_A` or `W_D`) is
   decremented. There is no need to keep track of planes once they
   have arrived or departed. Additionally, once a plane is waiting to
   arrive or depart, it continues waiting until it has arrived or
   departed.

4. It takes 5 minutes for a plane to arrive or depart. During these 5
   minutes, no other plane may use the runway. We can keep track of
   how long a plane has been on the runway with the
   `Runway_Counter`. If the `Runway_Counter` is at 0, then there is
   currently no plane using the runway, and it is clear for another
   plane to begin arriving or departing. Once the `Runway_Counter`
   reaches 5, we can reset it at the next clock tick. One clock tick
   represents 1 minute.

5. If there is at least one plane waiting to depart and no cars
   waiting to arrive, then the runway is set to departure mode (and
   vice versa for arrivals).

6. If both modes of the runway are inactive and planes become ready to
   depart and arrive simultaneously, the runway will activate arrival
   mode first. If the runway is in arrival mode and there are planes
   waiting to depart, no more than 3 planes may arrive from that time
   point. When either no more planes are waiting to arrive or 3 planes
   have arrived, the runway switches to departure mode. If the runway
   is on arrival mode and no planes are waiting to depart, then the
   runway may stay in arrival mode until a plane is ready to depart,
   from which time the 3-plane limit is imposed (and vice versa for
   departures). Put simply, if any planes are waiting for a mode that
   is inactive, that mode will become active no more than 15 minutes
   later (5 minutes for each of 3 planes).

To encode all this in CN, we first need a way to describe the state of
the runway at a given time. We can use a _struct_ that includes the
following fields:

- `ModeA` and `ModeD` to represent the arrival and departure modes,
  respectively. We can define constants for `ACTIVE` and `INACTIVE`,
  as described in the `Constants` section above.

- `W_A` and `W_D` to represent the number of planes waiting to arrive
  and depart, respectively.

- `Runway_Time` to represent the time (in minutes) that a plane has
  spent on the runway while arriving or departing.

- `Plane_Counter` to represent the number of planes that have arrived
  or departed while planes are waiting for the other mode. This will
  help us keep track of the 3-plane limit as described in _(6)_.

```c title="exercises/runway/state.h"
--8<--
exercises/runway/state.h
--8<--
```

Next, we need to specify what makes a state valid. We must define a
rigorous specification in order to ensure that the runway is always
safe and working as intended. Try thinking about what this might look
like before looking at the code below.

```c title="exercises/runway/valid_state.h"
--8<--
exercises/runway/valid_state.h
--8<--
```

Let's walk through the specifications in `valid_state`:

- The first two lines ensure that both modes in our model behave as intended: they can only be active or inactive. Any other value for these fields would be invalid.

- The third line says that either arrival mode or departure mode must be inactive. This specification ensures that the runway is never in both modes at the same time.

- The fourth line says that the number of planes waiting to arrive or depart must be non-negative. This makes sense: we can't have a negative number of planes!

- The fifth line ensures that the runway time is between 0 and 5. This addresses how a plane takes 5 minutes on the runway as described in _(4)_.

- The sixth line ensures that the plane counter is between 0 and 3. This is important for the 3-plane limit as described in _(6)_.

- The seventh line refers to the state at the beginning of the day. If both modes are inactive, then the day has just begun, and thus no planes have departed yet. This is why the plane counter must be 0.

- The eighth line says that if there is a plane on the runway, then one of the modes must be active. This is because a plane can only be on the runway if it is either arriving or departing.

- The final two lines ensure that we are incrementing `Plane_Counter` only if there are planes waiting for the other mode, as described in _(6)_.

Now that we have the tools to reason about the state of the runway formally, let's start writing some functions.

First, let's look at an initialization function and functions to update `Plane_Counter`. Step through these yourself and make sure you understand the reasoning behind each specification.

```c title="exercises/runway/funcs1.h"
--8<--
exercises/runway/funcs1.h
--8<--
```

_Exercise_: Now try adding your own specifications to the following
functions. Make sure that you specify a valid state as a pre- and
post-condition for every function. If you get stuck, the solution is
in the solutions folder.

```c title="exercises/runway/funcs2.c"
--8<--
exercises/runway/funcs2.c
--8<--
```

<!-- ====================================================================== -->

## Acknowledgment of Support and Disclaimer

This material is based upon work supported by the Air Force Research Laboratory (AFRL) and Defense Advanced Research Projects Agencies (DARPA) under Contract No. FA8750-24-C-B044, a European Research Council (ERC) Advanced Grant “ELVER” under the European Union’s Horizon 2020 research and innovation programme (grant agreement no. 789108), and additional funding from Google. The opinions, findings, and conclusions or recommendations expressed in this material are those of the authors and do not necessarily reflect the views of the Air Force Research Laboratory (AFRL).

<!-- ====================================================================== -->

<!--
Further topics:

- doubly linked lists
- Trees: - deep copy - sum - maybe the accumulating sum
- cn_function
- pack
- bitwise functions (operators are not present in the logical language)
- "ownership" in Rust vs. CN
- tips amnd tricks --
  cf. [](https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-verification)
- more data structures to try out
  [](https://www.geeksforgeeks.org/data-structures/#most-popular-data-structures)
- Maybe add some explanation of -- or at least a pointer to --
  Dhruv's Iris-in-C examples:
  pop_queue_lemma_stages.c
  push_queue_induction.c
  pop_queue_unified.c

Further exercises:

- Some exercises that get THEM to write predicates, datatype
  declarations, etc.

Misc things to do:

- replace 0 with NULL in specs

- naming issues - rename == to ptr_eq everywhere in specs - rename list to List in filenames. or go more radical and rename List to cnlist - consider renaming SLList_At to just List (and sllist to just list,
  etc.) everywhere (since we are only dealing with one kind of list
  in the tutorial, the extra pedantry is not getting us much; and
  this simplification would avoid trying to fix conventions that all
  CN code should use everywhere...)

  - related: the name Cons is awkward for several reasons:
    - long / verbose (nothing to do about that, I guess)
    - Seq is capitalized, but it means List
    - most important part is buried in the middle
    - What are the established C conventions here??

- some of the examples use int while the exercises that follow use
  unsigned int. This is a needless source of potential confusion.

- everyplace we do storage allocation, we should really allow the
  malloc call to return NULL if it wants to; the caller should
  explicitly check that it didn't get back NULL. This requires
  defining an "exit" function" with trivial pre- and postconditions
  (true / false).

- In queue.c, when I tried /_@ unfold QueueAux (F.front, F.back,
  B.first); @_/ I was confused by "the specification function
  `QueueAux' is not declared". I guess this is, again, the
  distinction between functions and predicates...?

- In debugging the queue example, The fact that some of the
  constraints in the error report are forced while others are random
  values filled in by the SMT solver is pretty problematic...

---

For later:

Alternative formatting tools to consider at some point (not now!):
probably the best fit:
[](https://myst-parser.readthedocs.io/en/latest/)
another very standard one to consider:
alternative: [](https://www.sphinx-doc.org/en/master/index.html)

Misc notes:

- Nb: take V = RW<t>(p) === p |-t-> V
-->
