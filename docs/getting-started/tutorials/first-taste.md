# Specifications

Suppose we are writing a function `min3`, which takes three `int` arguments.

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
exercises/min3/min3.test.partial.c
--8<--
```

In more detail...

- Function specifications are written inside special `/*@ ... @*/`
  comments, placed between the function argument list and the function
  body.

- The keyword `ensures` introduces the function's _postcondition_ --
  that is, a logical statement that should be true when the function returns.

- The keyword `return` refers to the return value.

- CN provides a variety of arithmetic and logical operators, which we
  use here to state that the return value should be less than or equal
  to each of the three inputs.

- Each clause of the specification concludes with a semicolon.

Next, suppose we have implemented `min3` (not quite correctly) as
shown below. 

```c title="exercises/min3/min3.broken.c"
--8<--
exercises/min3/min3.broken.c
--8<--
```

How can we figure out if our implementation satisfies our
specification? We can test it! Run the command `cn test <filename>` to
produce an output along these lines:

<span style="color:red">
BCP: Refresh this:
</span>

```
$ cn test min3.broken.c

Compiled 'min3_test.c'.
Compiled 'min3-exec.c'.
Compiled 'cn.c'.

Linked C *.o files.

Using seed: 50c34e798b33622c
Testing min3::min3: 2 runs
FAILED

...

original source location:
/*@ ensures return <= x
            ^~~~~~~~~~~ min3.c:2:13-4:28
CN assertion failed.


Testing Summary:
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
encountered.

We can do <span style="color:red">
(what do we need to do??)
</span>
to see our counterexample inputs:
```
x = 13
y = 4
z = 9
```

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

Testing Summary:
cases: 1, passed: 1, failed: 0, errored: 0, skipped: 0
```

Hooray!

## Exercises

_Refining the specification of `min3`_: The specification we wrote is
a bit loose: It says the result value should be smaller than `x`, `y`,
and `z`, but it does not say that it must be equal to one of these.
For example, a function that always returns `0` would satisfy this
spec specification. Improve it.

_Exercise._ Practice the workflow of specifying and testing the function `add`.

- Write a specification with the postcondition that `add` should
  return the sum of its inputs. Remember that CN supports standard
  arithmetic and boolean operators such as `+` and `==`. 
- Write an _incorrect_ implementation of `add` and check that `cn test` fails.
- Write a _correct_ implementation and check that `cn test` succeeds.

```c title="exercises/add.partial.c"
--8<--
exercises/add.partial.c
--8<--
```

