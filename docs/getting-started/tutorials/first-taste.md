# A First Taste of CN: Specification and Testing

This section introduces two of the most basic features of CN:   

- A notation for writing _specifications_ of C functions, and  
- A tool for _testing_ the behavior of the code against those specifications.

## A First Specification

Suppose we want to write a function `min3`, which takes three `unsigned int` arguments
and returns the smallest of the three.

```c title="exercises/min3/min3.partial.c"
--8<--
exercises/min3/min3.partial.c
--8<--
```

The desired behavior of `min3` is to return the smallest of the three inputs.
We expect, then, that the return value should be less than or equal to
each of`x`, `y`, and `z`. Using CN specifications, we can state this
formally and attach it directly 
to the function using a special comment block `/*@ ... @*/`:

```c title="exercises/min3/min3.partial1.c"
--8<--
exercises/min3/min3.partial1.c
--8<--
```

Let’s break this down...

- Function specifications are written inside a special comment block 
  `/*@ ... @*/` and placed between the function argument list and the
  function body. 

- The keyword `ensures` introduces the function's _postcondition_ --
  that is, a logical statement that we expect should be true when the
  function returns.

- The keyword `return` refers to the function's return value in the
  postcondition.

- CN provides a variety of arithmetic and logical operators, which we
  use here to state that the return value should be less than or equal
  to each of the three inputs.

- Each clause of the specification concludes with a semicolon.

{{ later("AZ: Since these terms might be unfamiliar to a practicing software engineer, 
it can be useful to explain more about pre- and post-conditions in an aside, or by 
linking references to it. For example wiki references might be enough: 
https://en.wikipedia.org/wiki/Precondition and
https://en.wikipedia.org/wiki/Postcondition") }}

{{ later("BCP: Sure.  We could also add a little more material here --
e.g., another example or two focused just on thinking about pre- and
postconditions.  But let's leave that for a later pass.") }} 

This gives us a clear, machine-checkable description of what the function is supposed to
do — not how it does it. Next, suppose we have implemented `min3` _incorrectly_ as
shown below.

```c title="exercises/min3/min3.broken.c"
--8<--
exercises/min3/min3.broken.c
--8<--
```
This function contains a subtle bug: in the second case, where `y` is the smallest,
it accidentally returns `x` instead. From a quick glance, the code looks reasonable — it
has the right structure — and the mistake is subtle and can go
uncaught. That’s where 
specification-based testing becomes useful.

## Testing

How can we find out whether our implementation satisfies our
specification? We can test it! 

This is one of the big ideas behind CN: once you’ve written a specification, CN can
generate test inputs and check whether the implementation behaves correctly for those
inputs.

For example, if the `min3` function ever returns a value that violates the specification
(like returning `x` when `y` is the smallest), CN will notice and report it — giving
concrete test inputs that fail the test (by violating the specifications).

Specification-based testing shifts the focus from writing tests manually, to letting the
specification drive the testing process. This approach can be more effective at catching
bugs. Specification-based testing can be used in different modes:

- _point testing_ similar to standard unit testing, but instead of predicting the
  expected output, the specification is used to judge whether the result is correct.
- _specification-based random testing_ which is essentially standard property-based
  testing (PBT).
{{ later("AZ: Perhaps expand on PBT or add a reference to PBT.") }} 

### Running `cn test`

To test the implementation, CN’s command-line tool can be invoked as `cn test <filename>`.
!!! tip
    To open a terminal inside VSCode (which will ensure your paths are set up correctly, 
    etc.), use `View > Terminal`.


```
$ cn test min3.broken.c

Testing min3::min3: 1 runs
FAILED

************************ Failed at *************************
function min3, file ./min3.broken-exec.c, line 55
original source location:
/*@ ensures return <= x
            ^~~~~~~~~~~ min3/min3.broken.c:2:13-4:28

********************** Failing input ***********************

unsigned int x = (unsigned int)(10);
unsigned int y = (unsigned int)(2);
unsigned int z = (unsigned int)(14);
min3(x, y, z);

************************************************************

cases: 1, passed: 0, failed: 1, errored: 0, skipped: 0
```

CN reports that there seems to be an issue with our
implementation. We'll return to that in a second, but first, let's
explain what happened when we ran `cn test`.

#### Property-Based Random Testing vs Input-Output Testing

You may be accustomed to input-output testing, where the developer writes _unit tests_
that assert what the output of a function should be on a given input.
Though CN also supports a similar approach, here, CN uses a different approach called
_property-based random testing_. With property-based random testing, things are much more
automatic. CN works in two important ways:

{{ todo("BCP: Again, CN also supports 'specification-based unit
testing' (or whatever it should be called -- I'm sure we don't
actually want to call it that!).  However, I don't think we want to
spend time here showing people how to do unit testing with CN -- that
should come later, IMO.  Namely, it should be introduced as a tool to
use to increase test coverage and/or deal with situations where the
random testing is not doing a good enough job of finding bugs.") }}

{{ later("AZ: Modified the text above to highlight the 2 different approaches.
          Need to address BCP's above comments about increasing test coverage.") }}


1.  First, instead of requiring the developer to manually construct a suite of interesting
    test _inputs_, CN automatically generates a large number of random test inputs.
2.  Second, instead of requiring the developer to manually calculate the expected _output_
    for each test input, CN uses the provided specification to check whether the program's
    behavior is satisfactory.

In other words, you tell CN what properties the function should satisfy (e.g., "the
result should be less than equal to x, y, and z"), and CN checks whether your
implementation always satisfies them.

#### What Went Wrong?

For our example, `cn test` generates three integer inputs, runs `min3` on these
inputs, and checks that the output satisfies the postcondition: 
```
     return <= x
  && return <= y
  && return <= z
```
It repeats this process until either some number of
tests (by default, 100) succeed or else a failing test, called a _counterexample_, is
encountered.  In the latter case, the counterexample is printed out as a snippet of
C code that will recreate the failure. 

Our run of `cn test min3.broken.c` found the counterexamples as
`x = 10`, `y = 2`, and `z = 14`. This is highlighted under failing input:
```
********************** Failing input ***********************

unsigned int x = (unsigned int)(10);
unsigned int y = (unsigned int)(2);
unsigned int z = (unsigned int)(14);
min3(x, y, z);

************************************************************
```

The counterexample you will see if you run the tests yourself will
most likely be different, due to randomness, but the debugging logic
will be the same.

Given these inputs `x = 10`, `y = 2`, and `z = 14`, we expect the function to
enter this branch:

```c
    else if (y <= x && y <= z) {
        return x;
    }
```

Aha! Here is the mistake: we should `return y`, not `x`, in this case.
Let's fix the bug:

```c title="exercises/min3/min3.fixed.c"
--8<--
exercises/min3/min3.fixed.c
--8<--
```

Now, if we run `cn test` again, the output should end with this message that the
tests passed:

```
$ cn test min3.fixed.c

Testing min3::min3: 100 runs
PASSED
```

Hooray!

### Exercises

_Exercise:_ Improve the specification.

The specification we wrote is
a bit loose: It says the result value should be smaller than `x`, `y`,
and `z`, but it does not say that it must be equal to one of these.
For example, a function that always returns `0` would satisfy this
specification. Improve it.

{{ later("JWS: Should explain at some point how to write multiple ensures clauses without ANDing everything etc.") }}

_Exercise:_ Practice the workflow of specifying and testing the function `add`.

Try the CN workflow on a simple function that adds two numbers.

```c title="exercises/add.partial.c"
--8<--
exercises/add.partial.c
--8<--
```

- Write a specification with the postcondition that `add` should
  return the sum of its inputs. Remember that CN supports standard
  arithmetic and boolean operators such as `+` and `==`.
- Write a _correct_ implementation and check that `cn test` succeeds.
- Write an _incorrect_ implementation of `add` and check that `cn test` fails.
- Bonus: Can you write an incorrect implementation of `add` for which testing
  will (incorrectly) succeed — i.e., such that `cn test` cannot find a
  counterexample after 100 tests?


## Specifications with Preconditions

Sometimes, a function is only meant to work under certain conditions. We can express
these assumptions using a precondition.
As an example, here's a silly way of writing a function that
returns whatever number it is given as input:

```c title="exercises/id_by_div/id_by_div.broken.c"
--8<--
exercises/id_by_div/id_by_div.broken.c
--8<--
```

If we try to `cn test` this function, however, we will get a counterexample such as this one:
```
x = 7
```

Oh! Because integer division is truncating, our silly function will
only work as desired when the input `x` is even. We can add this
requirement as a _precondition_, using the `requires` keyword.

```c title="exercises/id_by_div/id_by_div.fixed.c"
--8<--
exercises/id_by_div/id_by_div.fixed.c
--8<--
```

This updated specification says: _as long as `x` is even, the function must return `x`_.

A specification with both preconditions and postconditions says: if
the preconditions hold at the point where the function is called, then the
postconditions will hold when the function returns.


The other new piece of syntax here is the `u32` type annotations. In
CN specifications, numeric types need to be annotated explicitly, and
we use `u32` for `unsigned int`.  Try removing the annotations to see
the error message that results.

### Exercises

_Exercise:_ Fix the specification in the following example by adding a
precondition on 
the inputs `x` and `n` (don't change the postcondition or implementation).
Check that `cn test` succeeds.

```c title="exercises/id_by_div/id_by_div_n.broken.c"
--8<--
exercises/id_by_div/id_by_div_n.broken.c
--8<--
```

_Exercise_: Write a specification for the following function that says
the result is between arguments `p` and `q` (where `p` is less than or
equal to `q`), but that does not reveal the precise value of the
result.  That is, the same specification should work for a
function that returns `p`  or `(p+q)/2` instead of `q`.  

```c title="exercises/between.c"
--8<--
exercises/between.c
--8<--
```

