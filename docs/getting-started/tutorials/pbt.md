Suppose we are writing a function `min3`, which takes three `int` arguments.

```c title="exercises/min3/min3.orig.c"
--8<--
exercises/min3/min3.orig.c
--8<--
```

The desired behavior of `min3` is to return the smallest of the three inputs. That is, the return value should be less than or equal to `x` and to `y` and to `z`. More formally:

```c title="exercises/min3/min3.test.c"
--8<--
exercises/min3/min3.test.c
--8<--
```

In detail:

- Function specifications are given using special `/*@ ... @*/` comments, placed in-between the function argument list and the function body.

- The keyword `ensures` indicates the postcondition.

- The keyword `return` refers to the return value.

- CN provides a variety of arithmetic and logical operators, which we use here to require that the return value is less than or equal to each of the three inputs.

- Each clause of the specification concludes with a semicolon.

Next, suppose we have implemented `min3` as shown below.

```c title="exercises/min3/min3.test.broken.c"
--8<--
exercises/min3/min3.test.broken.c
--8<--
```

How can we figure out if our implementation satisfies our specification? We can test it! Run the command `cn test <filename>` to produce this output:
