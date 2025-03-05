# CN Basics

In this chapter, we will practice writing and testing specifications for simple arithmetic functions.

_Exercise._ Practice the workflow of specifying and testing the function `add`.

- Write a specification with the postcondition that `add` should return the sum of its inputs. Remember that CN supports standard arithmetic and boolean operators such as `+` and `==`.
- Write an incorrect implementation, and check that `cn test` fails.
- Write a correct implementation, and check that `cn test` succeeds.

```c title="exercises/add.partial.c"
--8<--
exercises/add.partial.c
--8<--
```

### Preconditions

Let's walk through an example that will introduce a few more CN specification features. Here's a silly way of writing a function that (we claim) returns the same value as its input:

```c title="exercises/id_by_div.broken.c"
--8<--
exercises/id_by_div.broken.c
--8<--
```

If we try to `cn test` this function, however, we will get a counterexample such as this one:

```
x = 7
```

Oh! Because integer division is truncated, our function will only work as desired when the input `x` is even. We can add this requirement as a _precondition_, using the `requires` keyword.

```c title="exercises/id_by_div.fixed.c"
--8<--
exercises/id_by_div.fixed.c
--8<--
```

That is, a specification with preconditions and postconditions asserts that if the preconditions held prior to the function call, then the postconditions will hold after the function returns.

The other new piece of syntax here is the `u32` type annotations. In CN specifications, numeric types need to be annotated explicitly, and we use `u32` for `unsigned int`. (As we will see later, we use `i32` for `int`.) Try removing the annotations to see the error message.

_Exercise._ Without changing the postcondition or implementation, fix the specification by adding a precondition on the inputs `x` and `n`. Check that `cn test` succeeds.

```c title="exercises/id_by_div_n.broken.c"
--8<--
exercises/id_by_div_n.broken.c
--8<--
```