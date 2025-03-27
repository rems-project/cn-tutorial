# (Verification) Allocating and Deallocating Memory

## Verification with malloc and free

<span style="color:red">
BCP: Needs text
</span>

```c title="exercises/malloc.h"
--8<--
exercises/malloc.h
--8<--
```

(Alternatively we can include an implementation written in arbitrary C
inside a CN file by marking it with the keyword `trusted` at the top
of its CN specification.)

Similarly:

```c title="exercises/free.h"
--8<--
exercises/free.h
--8<--
```

```c title="exercises/slf17_get_and_free.c"
--8<--
exercises/slf17_get_and_free.c
--8<--
```
