# Allocating and Deallocating Memory

Our next topic is programs that use dynamically allocated heap memory.

## Malloc and Free

Heap-using programs in CN can be written in almost exactly the same
way as in vanilla C.  The only difference is that, instead of calling
`malloc` and `free`, programs should call `cn_malloc` and `cn_free_sized`.
These are CN-specific versions of the usual `malloc` and `free` that
do some testing-related bookkeeping in addition to their main job of
allocating or deallocating heap memory.  The second argument to
`cn_free_sized` is the size of the structure being freed, same as the
argument to `cn_malloc`.

```c title="exercises/cn_malloc.h"
--8<--
exercises/cn_malloc.h
--8<--
```

Using `cn_malloc` and `cn_free_sized`, we can write higher-level programs
that manipulate the heap, as usual.

```c title="exercises/slf17_get_and_free.test.c"
--8<--
exercises/slf17_get_and_free.test.c
--8<--
```


### Exercises

_Exercise:_ Write a specification for the following program that returns a
pointer to a number that is the number pointed to by its argument `+ 1`.

```c title="exercises/slf_greater.test.c"
--8<--
exercises/slf_greater.test.c
--8<--
```