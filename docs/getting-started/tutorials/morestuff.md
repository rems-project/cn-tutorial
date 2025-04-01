# Additional / Homeless

This file collects some material that may or may not be useful long term.

## A safer allocation idiom

We can also define a "safer", ML-style version of `malloc` that
handles both allocation and initialization:
{{ todo("BCP: Are these worth the trouble to present?  C programmers will not find them
interesting, I guess.") }}

```c title="exercises/ref.h"
--8<--
exercises/ref.h
--8<--
```

{{ todo("TODO: BCP: This example is a bit broken: the file `slf0_basic_incr.c` does not appear at all in the tutorial, though a slightly different version (with signed numbers) does...") }}

```c title="exercises/slf16_basic_succ_using_incr.c"
--8<--
exercises/slf16_basic_succ_using_incr.c
--8<--
```

### Exercises

Write a specification for the following program that reveals _only_
that it returns a pointer to a number that is greater than the number
pointed to by its argument.

```c title="exercises/slf_ref_greater.c"
--8<--
exercises/slf_ref_greater.c
--8<--
```

## Alternate syntax for external functions

Here is another syntax for external / unknown
functions, together with an example of a loose specification:

```c title="exercises/slf18_two_dice.c"
--8<--
exercises/slf18_two_dice.c
--8<--
```
