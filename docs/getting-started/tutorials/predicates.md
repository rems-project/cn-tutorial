# Defining Predicates

{{ todo("BCP: The text becomes a bit sketchy from here on! But hopefully there's
still enough structure here to make sense of the examples...") }}

Suppose we want to write a function that takes _two_ pointers to
integers and increments the contents of both of them.

First, let's deal with the "normal" case where the two arguments do
not alias...

```c title="exercises/slf_incr2_noalias.c"
--8<--
exercises/slf_incr2_noalias.c
--8<--
```

But what if they do alias? The clunky solution is to write a whole
different version of `incr2` with a different embedded specification...

```c title="exercises/slf_incr2_alias.c"
--8<--
exercises/slf_incr2_alias.c
--8<--
```

This version does correctly state that the final values of `p` and `q` are, respectively, `3` and `1` more than their original values. But the way we got there -- by duplicating the whole function `incr2`, is horrible.

A better way is to define a _predicate_ that captures both the aliased
and the non-aliased cases together and use it in the pre- and
postconditions:

```c title="exercises/slf_incr2.test.c"
--8<--
exercises/slf_incr2.test.c
--8<--
```

{{ todo("BCP: Needs quite a few more words.") }}

{{ todo("BCP: We haven't introduced CN records. In particular, C programmers may be surprised that we don't have to pre-declare record types.") }}
