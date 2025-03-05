# Defining Predicates

<span style="color:red">
 We should show how to define predicates earlier -- 
</span>
<span style="color:red">
 - e.g., with numeric ranges!! 
</span>

<span style="color:red">

TODO: BCP: The text becomes a bit sketchy from here on! But hopefully there's
still enough structure here to make sense of the examples...

</span>

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

This version does correctly state that the final values of `p` and `q` are,m respectively, `3` and `1` more than their original values. But the way we got there -- by duplicating the whole function `incr2`, is horrible.

<span style="color:red">
Sainati: I think it would be useful here to add an explanation for how CN's type checking works. 
</span>
<span style="color:red">
 For example, in the definition of BothOwned here, how is CN able to prove that `take pv = Owned<unsigned int>(p);` 
</span>
<span style="color:red">
 type checks, since all we know about `p` in the definition of the predicate is that it's a pointer? 
</span>

A better way is to define a _predicate_ that captures both the aliased
and the non-aliased cases together and use it in the pre- and
postconditions:

<span style="color:red">
Sainati: I think it would be useful here to add an explanation for how CN's type checking works. 
</span>
<span style="color:red">
 For example, in the definition of BothOwned here, how is CN able to prove that `take pv = Owned<unsigned int>(p);` 
</span>
<span style="color:red">
 type checks, since all we know about `p` in the definition of the predicate is that it's a pointer? 
</span>

```c title="exercises/slf_incr2.c"
--8<--
exercises/slf_incr2.c
--8<--
```

<span style="color:red">
BCP: "BothOwned" is a pretty awkward name. 
</span>
<span style="color:red">
BCP: We haven't introduced CN records. In particular, C programmers may be surprised that we don't have to pre-declare record types. 
</span>
<span style="color:red">
BCP: the annotation on incr2 needs some unpacking for readers!! 
</span>
<span style="color:red">
BCP: first use of the "split_case" annotation 
</span>


