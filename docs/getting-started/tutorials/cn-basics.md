# More CN Basics

In this chapter, we will practice writing and testing specifications for simple arithmetic functions.

_Exercise: Add._ Practice the workflow of specifying and testing the function `add`.

- Add a specification that the function should return the sum of the inputs.
- Write an incorrect implementation, and check that `cn test` fails.
- Write a correct implementation, and check that `cn test` succeeds.

```c title="exercises/add.partial.c"
--8<--
exercises/add.partial.c
--8<--
```

Let's walk through an example that will introduce a few more CN specification features. [div 2 mul 2]

[sub 2 add 2]