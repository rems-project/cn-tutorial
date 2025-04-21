---
flow: Verification
---

# Arrays and loops, verified

Recall this specification for a simple function that reads from an array:

```c title="exercises/array_load.test.c"
--8<--
exercises/array_load.test.c
--8<--
```

This specification should ensure that the access `p[i]`
is safe. However, running `cn verify` on the example produces an
error: CN is unable to find the required ownership for reading `p[i]`.

```
[1/1]: read -- fail
solutions/array_load.test.c:10:10: error: `&p[(u64)i]` out of bounds
  return p[i];
         ^~~~
(UB missing short message): UB_CERB004_unspecified__pointer_add
```

The reason is that, when searching for a required resource, such as
the `RW` resource for `p[i]` here, CN’s resource inference does not
consider iterated resources. Quantifiers, as used by iterated
resources, can make verification undecidable, so, in order to maintain
predictable type checking, CN delegates this aspect of the reasoning
to the user.

To make the `RW` resource required for accessing `p[i]` available to
CN’s resource inference, we have to explicitly "`focus`" ownership for
index `i` out of the iterated resource.

```c title="exercises/array_load.c"
--8<--
exercises/array_load.c
--8<--
```

The CN comment `/*@ focus RW<unsigned int>, i; @*/` is a proof hint in the form of a "ghost statement" that instructs CN to instantiate any available iterated `RW<unsigned int>` resource for index `i`. In our example this operation splits this iterated resource

```c
each(u32 j; j < n) { RW<unsigned int>(array_shift<unsigned int>(p,j)) }
```

into two parts:

1. the instantiation of the iterated resource at `i`

```c
RW<unsigned int>(array_shift<unsigned int>(p,i))
```

2. the remainder of the iterated resource, the ownership for all indices except `i`

```c
  each(u32 j; j < n && j != i)
  { RW<unsigned int>(array_shift<unsigned int>(p,j)) }
```

After this extraction step, CN can use the (former) extracted resource to justify the access `p[i]`. Note that an `focus` statement's second argument can be any arithmetic expression, not just a single identifier like in this example.

Following a `focus`, CN remembers the extracted index and can automatically "reverse" the extraction when needed, merging the resources  when ownership of the full array is required.
<!--
 after type checking the access `p[i]` CN must ensure the function’s postcondition holds, which needs the full array ownership again (including the extracted index `i`); remembering the index `i`, CN then automatically merges resources (1) and (2) again to obtain the required full array ownership, and completes the verification of the function. -->

### Exercises

_Exercise:_ Add `focus` statements to verify your specification of `array_swap` from last chapter.

```c title="exercises/array_swap.c"
--8<--
exercises/array_swap.c
--8<--
```

{{ todo("BCP: I wrote the following, which seemed natural but did not
work -- I still don't fully understand why. I think this section will
need some more examples / exercises to be fully digestible, or perhaps
this is just yet another symptom of my imperfect understanding of how
the numeric stuff works.

    void array_swap (unsigned int *p, unsigned int n, unsigned int i, unsigned int j)
    /*@ requires take a1 = each(i32 k; 0i32 <= k && k < n) { RW<unsigned int>(array_shift<unsigned int>(p,k)) };
                 0i32 <= i && i < n;
                 0i32 <= j && j < n;
                 j != i;
                 take xi = RW<unsigned int>(array_shift(p,i));
                 take xj = RW<unsigned int>(array_shift(p,j))
        ensures take a2 = each(i32 k; 0i32 <= k && k < n) { RW<unsigned int>(array_shift<unsigned int>(p,k)) };
                a1[i:xj][j:xi] == a2
    @*/
    {
      focus RW<unsigned int>, i;
      focus RW<unsigned int>, j;
      unsigned int tmp = p[i];
      p[i] = p[j];
      p[j] = tmp;
    }
") }}


_Exercise:_ Specify and verify the following function, `array_read_two`, which takes the base pointer `p` of an `unsigned int` array, the array length `n`, and two indices `i` and `j`. *Assuming `i` and `j` are different*, it returns the sum of the values at these two indices.

```c title="exercises/array_read_two.c"
--8<--
exercises/array_read_two.c
--8<--
```

### Loops

If we have array code with loops, CN requires the user to supply _loop invariants_ — CN specifications of the `RW` resources and constraints required to verify each iteration of the loop.

Let's take a look at a simple first example. The following function, `array_init`, takes the base pointer `p` of a `char` array and the array length `n` and writes `0` to each array cell.

```c title="exercises/array_init.c"
--8<--
exercises/array_init.c
--8<--
```

If we focus for now just on proving safe execution of `array_init`, a specification might look as above. This closely resembles specifications we have seen previously, but now with `char`s.

To verify this, we have to supply a loop invariant that specifies all resource ownership and the necessary constraints that hold before and after each iteration of the loop. Loop invariants are specified using the keyword `inv`, followed by CN specifications using the same syntax as in function pre- and postconditions. The variables in scope for loop invariants are all in-scope C variables, as well as CN variables introduced in the function precondition. _In loop invariants, the name of a C variable refers to its current value_ (more on this shortly).

```c title="solutions/array_init.c"
--8<--
solutions/array_init.c
--8<--
```

{{ later("Concrete syntax: Why not write something like \"unchanged
{p,n}\" or \"unchanged: p,n\"?") }}

The main condition here is unsurprising: we specify ownership of an iterated resource for an array just like in the the pre- and postcondition.

The second thing we need to do, however, is less straightforward. Recall that, as discussed at the start of the tutorial, function arguments in C are mutable. Although, in this example, it is obvious that `p` and `n` do not change, CN currently requires the loop invariant to explicitly state this, using special notation `{p} unchanged` (and similarly for `n`).

**Note.** If we forget to specify `unchanged`, this can lead to confusing errors. In this example, for instance, CN would verify the loop against the loop invariant, but would be unable to prove a function postcondition seemingly directly implied by the loop invariant (lacking the information that the postcondition's `p` and `n` are the same as the loop invariant's). Future CN versions may handle loop invariants differently and treat variables as immutable by default.

{{ later("BCP: This seems like a good idea!") }}

The final piece needed in the verification is an `focus` statement, as used in the previous examples: to separate the individual `RW<char>` resource for index `j` out of the iterated `RW` resource and make it available to the resource inference, we specify `focus RW<char>, j;`.

With the `inv` and `focus` statements in place, CN accepts the function.


{{ todo("JWS: removed second loop example because it is out of sync as we moved `W` resources later. could try to replace with something from the previous chapter") }}

<!-- ### Second loop example

The specification of `array_init` is overly strong: it requires an iterated `RW` resource for the array on entry. If, as the name suggests, the purpose of `array_init` is to initialise the array, then a precondition asserting only an iterated `W` resource for the array should also be sufficient. The modified specification is then as follows.

```c title="exercises/array_init2.c"
--8<--
exercises/array_init2.c
--8<--
```

This specification _should_ hold: assuming ownership of an uninitialised array on entry, each iteration of the loop initialises one cell of the array, moving it from `W` to `RW` "`state`", so that on function return the full array is initialised. (Recall that stores only require `W` ownership of the written memory location, i.e., ownership of not-necessarily-initialised memory.)

To verify this modified example we again need a loop Invariant. But
this time the loop invariant is more involved: since each iteration of
the loop initialises one more array cell, the loop invariant has to do
precise book-keeping of the initialisation status of the different
sections of the array.

To do this, we partition the array ownership into two parts: for each index of the array the loop has already visited, we have an `RW` resource, for all other array indices we have the (unchanged) `W` ownership.

```c title="solutions/array_init2.c"
--8<--
solutions/array_init2.c
--8<--
```

Let's go through this line-by-line:

- We assert ownership of an iterated `RW` resource, one for each index `i` strictly smaller than loop variable `j`.

- All remaining indices `i`, between `j` and `n` are still uninitialised, so part of the iterated `W` resource.

- As in the previous example, we assert `p` and `n` are unchanged.

- Finally, unlike in the previous example, this loop invariant involves `j`. We therefore also need to know that `j` does not exceed the array length `n`. Otherwise CN would not be able to prove that, on completing the last loop iteration, `j=n` holds. This, in turn, is needed to show that, when the function returns, ownership of the iterated `RW` resource --- as specified in the loop invariant --- is fully consumed by the function's post-condition and there is no left-over unused resource.

As before, we also have to instruct CN to `focus` ownership of individual array cells out of the iterated resources:

- to allow CN to focus the individual `W` to be written, we use `focus W<char>, j;`;

- the store returns a matching `RW<char>` resource for index `j`;

- finally, we add `focus RW<char>, j;` to allow CN to "`attach`" this
  resource to the iterated `RW` resource. CN issues a warning, because
  nothing is, in fact, extracted: we are using `focus` only for the
  "`reverse`" direction.  {{ later("Dhruv: See long explanation and
  issue here: rems-project/cerberus#498.  BCP: Would it be useful to
  bring any of that discussion here?") }} -->

### Exercises

**Init array reverse.** Verify the function `array_init_rev`, which has the same specification as `array_init2`, but initializes the array in decreasing index order (from right to left).

```c title="exercises/array_init_rev.c"
--8<--
exercises/array_init_rev.c
--8<--
```

{{ later("Another potential example / case study, involving nested iteration:
    https://github.com/rems-project/cerberus/issues/848#issuecomment-2702085128") }}
