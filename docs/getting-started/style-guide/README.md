# Style Guide

<span style="color:red">BCP: If we are agreed on the naming conventions suggested in /NAMING-CONVENTIONS.md, we could move that material here. </span>

!!! warning

    This is a draft of proposed style guidelines.  Expect this to change in the
    near future.

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


