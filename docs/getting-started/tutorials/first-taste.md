# A First Taste of CN

Suppose we are writing a function `min3`, which takes three `int` arguments.

```c title="exercises/min3/min3.partial.c"
--8<--
exercises/min3/min3.partial.c
--8<--
```

The desired behavior of `min3` is to return the smallest of the three inputs. That is, the return value should be less than or equal to `x` and to `y` and to `z`. More formally:

```c title="exercises/min3/min3.test.partial.c"
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

- CN provides a variety of arithmetic and logical operators, which we use here to require that the return value is less than or equal to each of the three inputs.

- Each clause of the specification concludes with a semicolon.

Next, suppose we have implemented `min3` as shown below.

```c title="exercises/min3/min3.test.broken.c"
--8<--
exercises/min3/min3.test.broken.c
--8<--
```

How can we figure out if our implementation satisfies our specification? We can test it! Run the command `cn test <filename>` to produce an output along these lines:

```
$ cn test min3.c

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

Hmm, it seems like there might be an issue with our implementation. We'll return to that in a second, but first, let's explain what happened when we ran `cn test`.

`cn test` does _property-based testing_. You may instead be accustomed to input-output testing, where the user manually writes unit tests that assert what the output of a function should be on a given input. With property-based testing, things are much more automatic. Test inputs are _randomly generated_, and then assessed against the specification (i.e., the "property").

Here, `cn test` generates three integer inputs, runs `min3` on these inputs, and checks that the output satisfies the postcondition. It repeats this process until either some number (by default, 100) of tests succeed, or a failing test, called a _counterexample_, is encountered.

We can do X to see our counterexample inputs:
```
x = 13
y = 4
z = 9
```
(The counterexample you generated is most likely different, due to randomness, but the debugging logic will be the same.)

Given these three inputs, we expect the function to enter this branch:

```c
    else if (y <= x && y <= z) {
        return x;
    }
```

Oops! We made a mistake here. We should `return y`, not `x`, in this case.
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

### Exercises

_Refining the specification of `min3`_: The specification we wrote is
a bit loose: It says the result value should be smaller than `x`, `y`,
and `z`, but it does not say that it must be equal to one of these.
For example, a function that always returns `0` would satisfy this
spec specification. Improve it.

??? note "(Optional) Verifying `min3`"
    Property-based testing is great for increasing our confidence that the function satisfies its specification, but we might also want to _verify_ this formally. Run `cn verify <filename>` on the buggy version to produce this output:

    ```
    [1/1]: min3 -- fail
    min3.c:11:9: error: Unprovable constraint
            return x;
            ^~~~~~~~~
    Constraint from min3.c:2:13:
    /*@ ensures return <= x
                ^~~~~~~~~~~
    State file: file:///var/folders/_5/81fbkyvn3n5dsm34qw2zpr7w0000gn/T/state__min3.c__min3.html
    ```

    And on the fixed version to produce this output:
    ```
    [1/1]: min3 -- pass
    ```

    Whereas `cn test` treats the function body as a black box, `cn verify` analyzes it directly, examining all possible paths through the code until it either succeeds in constructing a formal proof that the function satisfies the specification, or it encounters a constraint that cannot be satisfied.
