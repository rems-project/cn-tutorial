# A First Taste of CN: Specification and Testing

This section introduces the most basic features of CN: a notation for
writing _specifications_ of C functions and a tool for _testing_ the
behavior of the code against those specifications.

## A First Specification

Suppose we are writing a function `min3`, which takes three `unsigned int` arguments.

```c title="exercises/min3/min3.partial.c"
--8<--
exercises/min3/min3.partial.c
--8<--
```

The desired behavior of `min3` is to return the smallest of the three
inputs. We expect, then, that the return value should be less
than or equal to `x` and to `y` and to `z`. More formally:

```c title="exercises/min3/min3.partial1.c"
--8<--
exercises/min3/min3.partial1.c
--8<--
```

In more detail...

- Function specifications are written inside special `/*@ ... @*/`
  comments, placed between the function argument list and the function
  body.

- The keyword `ensures` introduces the function's _postcondition_ --
  that is, a logical statement that we expect should be true when the
  function returns.

- The keyword `return` refers to the function's return value in the
  postcondition.

- CN provides a variety of arithmetic and logical operators, which we
  use here to state that the return value should be less than or equal
  to each of the three inputs.

- Each clause of the specification concludes with a semicolon.

Next, suppose we have implemented `min3` (a little incorrectly) as
shown below.

```c title="exercises/min3/min3.broken.c"
--8<--
exercises/min3/min3.broken.c
--8<--
```

## Testing

How can we find out whether our implementation satisfies our
specification? We can test it!

Running the command `cn test <filename>` in a terminal will produce an output along
the following lines.  To open a terminal inside VSCode (which will
ensure your paths are set up correctly, etc.), use `View > Terminal`.

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

The `cn test` command does _property-based random testing_. You may
instead be accustomed to input-output testing, where the developer
writes _unit tests_ that assert what the output of a function should
be on a given input.  With property-based random testing, things are
much more automatic. First, instead of requiring the developer to
manually construct a suite of interesting test _inputs_, CN
automatically generates large number of random test inputs.  Second,
instead of requiring the developer to manually calculate the expected
_output_ for each test input, CN uses the provided specification to
check whether the program's behavior is satisfactory.

Here, `cn test` generates three integer inputs, runs `min3` on these
inputs, and checks that the output satisfies the postcondition. It
repeats this process until either some number (by default, 100) of
tests succeed or else a failing test, called a _counterexample_, is
encountered.  In this case, the counterexample is printed out in
the form of a snipped of C code that will recreate the failing
situation.

(The counterexample you will see if you run the tests yourself will
most likely be different, due to randomness, but the debugging logic
will be the same.)

Given these three inputs, we expect the function to enter this branch:

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

Now, if we run `cn test` again, the output should end with this message that the tests passed:

```
Testing min3::min3: 100 runs
PASSED
```

Hooray!

### Exercises

_Refining the specification of `min3`_: The specification we wrote is
a bit loose: It says the result value should be smaller than `x`, `y`,
and `z`, but it does not say that it must be equal to one of these.
For example, a function that always returns `0` would satisfy this
spec specification. Improve it.

_Exercise._ Practice the workflow of specifying and testing the function `add`.

- Write a specification with the postcondition that `add` should
  return the sum of its inputs. Remember that CN supports standard
  arithmetic and boolean operators such as `+` and `==`.
- Write a _correct_ implementation and check that `cn test` succeeds.
- Write an _incorrect_ implementation of `add` and check that `cn test` fails.
- Extra credit: Can you find a way to write an incorrect
  implementation of `add` for which testing will (incorrectly) succeed
  -- i.e., such that `cn test` cannot find a counterexample after 100
  tests?

```c title="exercises/add.partial.c"
--8<--
exercises/add.partial.c
--8<--
```

## Specifications with Preconditions

Here's a silly way of writing a function that
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

A specification with both preconditions and postconditions says that, if
the preconditions hold at the point where the function is called, then the
postconditions will hold when the function returns.

The other new piece of syntax here is the `u32` type annotations. In
CN specifications, numeric types need to be annotated explicitly, and
we use `u32` for `unsigned int`.  Try removing the annotations to see
the error message that results.

### Exercises

_Exercise._ Without changing the postcondition or implementation, fix
the specification in the following example by adding a precondition on
the inputs `x` and `n`. Check that `cn test` succeeds.

```c title="exercises/id_by_div/id_by_div_n.broken.c"
--8<--
exercises/id_by_div/id_by_div_n.broken.c
--8<--
```

_Exercise: A loose specification for `greater`_: Write a specification for this
function that says that the result is larger than the argument passed
to the function but that does not reveal the precise value of the
result.  (I.e., the same specification should work for a function that
adds `1000` instead of `42`.)  Be careful of overflow.
```c title="exercises/greater.c"
--8<--
exercises/greater.c
--8<--
```
<span style="color:red">
JWS: What is the envisioned solution to this exercise? I don't see how
to write a precondition without a) knowing what value is added
or b) knowing how to specify the max int.
</span>

<span style="color:red">
JWS: Can you decide a consistent way to label exercises? There are at least
three styles in this chapter. I prefer _Exercise._ (e.g. no Exercise sections,
no names.) because it's nice and short and I don't feel like the name adds.
</span>

<!-- BCP: Testing should fail for the version of this with no
precondition, but as of 3/27/25 it did not.  Does it now? -->

