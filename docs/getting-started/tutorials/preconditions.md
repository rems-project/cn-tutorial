# Preconditions

Next, let's walk through an example that will introduce a few more CN
specification features. Here's a silly way of writing a function that
returns whatever number it is given as input:

```c title="exercises/id_by_div.broken.c"
--8<--
exercises/id_by_div.broken.c
--8<--
```

If we try to `cn test` this function, however, we will get a counterexample such as this one:
<span style="color:red">
BCP: update this! 
</span>
```
x = 7
```

Oh! Because integer division is truncating, our silly function will
only work as desired when the input `x` is even. We can add this
requirement as a _precondition_, using the `requires` keyword.

```c title="exercises/id_by_div.fixed.c"
--8<--
exercises/id_by_div.fixed.c
--8<--
```

A specification with preconditions and postconditions asserts that, if
the preconditions hold at the point where the function is called, then the
postconditions will hold when the function returns.

The other new piece of syntax here is the `u32` type annotations. In
CN specifications, numeric types need to be annotated explicitly, and
we use `u32` for `unsigned int`.  Try removing the annotations to see
the error message.

_Exercise._ Without changing the postcondition or implementation, fix
the specification in the following example by adding a precondition on
the inputs `x` and `n`. Check that `cn test` succeeds.

```c title="exercises/id_by_div_n.broken.c"
--8<--
exercises/id_by_div_n.broken.c
--8<--
```
