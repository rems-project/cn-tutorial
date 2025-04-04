# Defining Predicates

<!-- We should show how to define predicates earlier -- -->
<!-- - e.g., with numeric ranges!! -->

<!--
TODO: BCP: The text becomes a bit sketchy from here on! But hopefully there's
still enough structure here to make sense of the examples...
-->

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

<!-- TODO: Sainati: I think it would be useful here to add an explanation for how CN's type checking works. -->
<!-- For example, in the definition of BothOwned here, how is CN able to prove that `take pv = Owned<unsigned int>(p);` -->
<!-- type checks, since all we know about `p` in the definition of the predicate is that it's a pointer? -->

A better way is to define a _predicate_ that captures both the aliased
and the non-aliased cases together and use it in the pre- and
postconditions:

<!-- TODO: Sainati: I think it would be useful here to add an explanation for how CN's type checking works. -->
<!-- For example, in the definition of BothOwned here, how is CN able to prove that `take pv = Owned<unsigned int>(p);` -->
<!-- type checks, since all we know about `p` in the definition of the predicate is that it's a pointer? -->

```c title="exercises/slf_incr2.c"
--8<--
exercises/slf_incr2.c
--8<--
```

<!-- TODO: BCP: "BothOwned" is a pretty awkward name. -->
<!-- TODO: BCP: We haven't introduced CN records. In particular, C programmers may be surprised that we don't have to pre-declare record types. -->
<!-- TODO: BCP: the annotation on incr2 needs some unpacking for readers!! -->
<!-- TODO: BCP: first use of the "split_case" annotation -->


