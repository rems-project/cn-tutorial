# Arrays and Loops

Another common datatype in C is arrays. Reasoning about memory ownership for arrays is more difficult than for the datatypes we have seen so far, for two reasons: (1) C allows the programmer to access arrays using _computed pointers_, and (2) the size of an array does not need to be known as a constant at compile time.

To support reasoning about code manipulating arrays and computed pointers, CN has _iterated resources_. For instance, to specify ownership of an `unsigned` array with 10 cells starting at pointer `p`, CN uses the following iterated resource:

```c
each (i32 i; 0i32 <= i && i < 10i32)
{ Owned<unsigned int>(array_shift<unsigned int>(p,i)) }
```

In detail, this can be read as follows:

- for each integer `i` of CN type `i32`, …

- if `i` is between `0` and `10`, …

- assert ownership of a resource `Owned<unsigned int>` …

- for cell `i` of the array with base-address `p`.

Here `array_shift<unsigned int>(p,i)` computes a pointer into the array at pointer `p`, appropriately offset for index `i`.

In general, iterated resource specifications take the form

```c
each (BT Q; GUARD) { RESOURCE }
```

comprising three parts:

- `BT Q`, for some CN type `BT` and name `Q`, introduces the quantifier `Q` of basetype `BT`, which is bound in `GUARD` and `RESOURCE`;

- `GUARD` is a boolean-typed expression delimiting the instances of `Q` for which ownership is asserted; and

- `RESOURCE` is any non-iterated CN resource.

### First array example

Let’s see how this applies to a simple array-manipulating function. Function `read` takes three arguments: the base pointer `p` of an `unsigned int` array, the length `n` of the array, and an index `i` into the array; `read` then returns the value of the `i`-th array cell.

```c title="exercises/array_load.broken.c"
--8<--
exercises/array_load.broken.c
--8<--
```

The CN precondition requires

- ownership of the array on entry — one `Owned<unsigned int>` resource for each array index between `0` and `n` — and
- that `i` lies within the range of owned indices.

On exit the array ownership is returned again.

<span style="color:red">
BCP: Split the file here.  In the testing variant, do several more
examples (e.g., maybe working up to sorting?).  
</span>

This specification, in principle, should ensure that the access `p[i]` is safe. However, running CN on the example produces an error: CN is unable to find the required ownership for reading `p[i]`.

<span style="color:red">
BCP: Update it
</span>
```
cn verify solutions/array_load.broken.c
[1/1]: read
build/solutions/array_load.broken.c:5:10: error: Missing resource for reading
return p[i];
^~~~
Resource needed: Owned<signed int>(array_shift<signed int>(p, (u64)i))
```

The reason is that, when searching for a required resource, such as the `Owned` resource for `p[i]` here, CN’s resource inference does not consider iterated resources. Quantifiers, as used by iterated resources, can make verification undecidable, so, in order to maintain predictable type checking, CN delegates this aspect of the reasoning to the user.

<span style="color:red">
BCP: This is more verification-relevant
</span>

To make the `Owned` resource required for accessing `p[i]` available to CN’s resource inference we have to explicitly "`extract`" ownership for index `i` out of the iterated resource.

```c title="exercises/array_load.c"
--8<--
exercises/array_load.c
--8<--
```

Here the CN comment `/*@ extract Owned<unsigned int>, i; @*/` is a proof hint in the form of a "`ghost statement`" that instructs CN to instantiate any available iterated `Owned<unsigned int>` resource for index `i`. In our example this operation splits the iterated resource into two:

```c
each(i32 j; 0i32 <= j && j < n) { Owned<unsigned int>(array_shift<unsigned int>(p,j)) }
```

is split into

1. the instantiation of the iterated resource at `i`

```c
Owned<unsigned int>(array_shift<unsigned int>(p,i))
```

2. the remainder of the iterated resource, the ownership for all indices except `i`

```c
  each(i32 j; 0i32 <= j && j < n && j != i)
  { Owned<unsigned int>(array_shift<unsigned int>(p,j)) }
```

After this extraction step, CN can use the (former) extracted resource to justify the access `p[i]`. Note that an `extract` statement's second argument can be any arithmetic expression, not just a single identifier like in this example.

Following an `extract` statement, CN remembers the extracted index and can automatically "`reverse`" the extraction when needed: after type checking the access `p[i]` CN must ensure the function’s postcondition holds, which needs the full array ownership again (including the extracted index `i`); remembering the index `i`, CN then automatically merges resources (1) and (2) again to obtain the required full array ownership, and completes the verification of the function.

So far the specification only guarantees safe execution but does not
specify the behaviour of `read`. To address this, let’s return to
the iterated resources in the function specification. When we specify
`take A = each ...` here, what is `A`? In CN, the output of an
iterated resource is a _map_ from indices to resource outputs. In this
example, where index `j` has CN type `i32` and the iterated
resource is `Owned<unsigned int>`, the output `A` is a map from `i32`
indices to `i32` values — CN type `map<i32,i32>`. If the type of
`j` was `i64` and the resource `Owned<char>`, `A` would have
type `map<i64,u8>`.

We can use this to refine our specification with information about the functional behaviour of `read`.

```c title="exercises/array_load2.c"
--8<--
exercises/array_load2.c
--8<--
```

We specify that `read` does not change the array — the outputs of `Owned`,
`A` and `A_post`, taken before and after running the function, are
the same — and that the value returned is `A[i]`.

### Exercises

_Array read two._ Specify and verify the following function, `array_read_two`, which takes the base pointer `p` of an `unsigned int` array, the array length `n`, and two indices `i` and `j`. Assuming `i` and `j` are different, it returns the sum of the values at these two indices.

<span style="color:red">
BCP: When we get around to renaming files in the examples directory,
we should call this one array_swap or something else beginning with
"array".  Or put it in a subdirectory.
</span>

```c title="exercises/add_two_array.c"
--8<--
exercises/add_two_array.c
--8<--
```

<span style="color:red">
BCP: In this one I got quite tangled up in different kinds of integers, then got tangled up in (I think) putting the extract declarations in the wrong place. (I didn't save the not-working version, I'm afraid.)
</span>

<span style="color:red">
Sainati: I think it would be useful to have a int array version of this exercise as a worked example; I am not sure, for example, how one would express bounds requirements on the contents of an array in CN, as you would need to do here to ensure that p[i] + p[j] doesn’t overflow if p's contents are signed ints
</span>

_Swap array._ Specify and verify `swap_array`, which swaps the values of two cells of an `unsigned int` array. Assume again that `i` and `j` are different, and describe the effect of `swap_array` on the array value using the CN map update expression `a[i:v]`, which denotes the same map as `a`, except with index `i` updated to `v`.

```c title="exercises/swap_array.c"
--8<--
exercises/swap_array.c
--8<--
```

<span style="color:red">

TODO: BCP: I wrote this, which seemed natural but did not work -- I still don't fully understand why. I think this section will need some more examples / exercises to be fully digestible, or perhaps this is just yet another symptom of my imperfecdt understanding of how the numeric stuff works.

    void swap_array (unsigned int *p, unsigned int n, unsigned int i, unsigned int j)
    /*@ requires take a1 = each(i32 k; 0i32 <= k && k < n) { Owned<unsigned int>(array_shift<unsigned int>(p,k)) };
                 0i32 <= i && i < n;
                 0i32 <= j && j < n;
                 j != i;
                 take xi = Owned<unsigned int>(array_shift(p,i));
                 take xj = Owned<unsigned int>(array_shift(p,j))
        ensures take a2 = each(i32 k; 0i32 <= k && k < n) { Owned<unsigned int>(array_shift<unsigned int>(p,k)) };
                a1[i:xj][j:xi] == a2
    @*/
    {
      extract Owned<unsigned int>, i;
      extract Owned<unsigned int>, j;
      unsigned int tmp = p[i];
      p[i] = p[j];
      p[j] = tmp;
    }


</span>

### Loops

The array examples covered so far manipulate one or two individual cells of an array. Another typical pattern in code working over arrays is to _loop_, uniformly accessing all cells of an array or a sub-range of it.

In order to verify code with loops, CN requires the user to supply loop invariants -- CN specifications of all owned resources and the constraints required to verify each iteration of the loop.

Let's take a look at a simple first example. The following function, `init_array`, takes the base pointer `p` of a `char` array and the array length `n` and writes `0` to each array cell.

<span style="color:red">
BCP: Rename to array_init.c 
</span>

```c title="exercises/init_array.c"
--8<--
exercises/init_array.c
--8<--
```

If, for the moment, we focus just on proving safe execution of `init_array`, ignoring its functional behaviour, a specification might look as above: on entry, `init_array` takes ownership of an iterated `Owned<char>` resource -- one `Owned` resource for each index `i` of type `u32` (so necessarily greater or equal to `0`) up to `n`; on exit `init_array` returns the ownership.

To verify this, we have to supply a loop invariant that specifies all resource ownership and the necessary constraints that hold before and after each iteration of the loop. Loop invariants are specified using the keyword `inv`, followed by CN specifications using the same syntax as in function pre- and postconditions. The variables in scope for loop invariants are all in-scope C variables, as well as CN variables introduced in the function precondition. _In loop invariants, the name of a C variable refers to its current value_ (more on this shortly).

```c title="solutions/init_array.c"
--8<--
solutions/init_array.c
--8<--
```

<span style="color:red">

TODO: BCP: Concrete syntax: Why not write something like "unchanged {p,n}" or "unchanged: p,n"?

</span>

The main condition here is unsurprising: we specify ownership of an iterated resource for an array just like in the the pre- and postcondition.

The second thing we need to do, however, is less straightforward. Recall that, as discussed at the start of the tutorial, function arguments in C are mutable. Although, in this example, it is obvious that `p` and `n` do not change, CN currently requires the loop invariant to explicitly state this, using special notation `{p} unchanged` (and similarly for `n`).

**Note.** If we forget to specify `unchanged`, this can lead to confusing errors. In this example, for instance, CN would verify the loop against the loop invariant, but would be unable to prove a function postcondition seemingly directly implied by the loop invariant (lacking the information that the postcondition's `p` and `n` are the same as the loop invariant's). Future CN versions may handle loop invariants differently and treat variables as immutable by default.

<span style="color:red">

TODO: BCP: This seems like a good idea!

</span>

The final piece needed in the verification is an `extract` statement, as used in the previous examples: to separate the individual `Owned<char>` resource for index `j` out of the iterated `Owned` resource and make it available to the resource inference, we specify `extract Owned<char>, j;`.

With the `inv` and `extract` statements in place, CN accepts the function.

### Second loop example

The specification of `init_array` is overly strong: it requires an iterated `Owned` resource for the array on entry. If, as the name suggests, the purpose of `init_array` is to initialise the array, then a precondition asserting only an iterated `Block` resource for the array should also be sufficient. The modified specification is then as follows.

```c title="exercises/init_array2.c"
--8<--
exercises/init_array2.c
--8<--
```

This specification _should_ hold: assuming ownership of an uninitialised array on entry, each iteration of the loop initialises one cell of the array, moving it from `Block` to `Owned` "`state`", so that on function return the full array is initialised. (Recall that stores only require `Block` ownership of the written memory location, i.e., ownership of not-necessarily-initialised memory.)

To verify this modified example we again need a loop Invariant. But
this time the loop invariant is more involved: since each iteration of
the loop initialises one more array cell, the loop invariant has to do
precise book-keeping of the initialisation status of the different
sections of the array.

To do this, we partition the array ownership into two parts: for each index of the array the loop has already visited, we have an `Owned` resource, for all other array indices we have the (unchanged) `Block` ownership.

```c title="solutions/init_array2.c"
--8<--
solutions/init_array2.c
--8<--
```

Let's go through this line-by-line:

- We assert ownership of an iterated `Owned` resource, one for each index `i` strictly smaller than loop variable `j`.

- All remaining indices `i`, between `j` and `n` are still uninitialised, so part of the iterated `Block` resource.

- As in the previous example, we assert `p` and `n` are unchanged.

- Finally, unlike in the previous example, this loop invariant involves `j`. We therefore also need to know that `j` does not exceed the array length `n`. Otherwise CN would not be able to prove that, on completing the last loop iteration, `j=n` holds. This, in turn, is needed to show that, when the function returns, ownership of the iterated `Owned` resource --- as specified in the loop invariant --- is fully consumed by the function's post-condition and there is no left-over unused resource.

As before, we also have to instruct CN to `extract` ownership of individual array cells out of the iterated resources:

- to allow CN to extract the individual `Block` to be written, we use `extract Block<char>, j;`;

- the store returns a matching `Owned<char>` resource for index `j`;

- finally, we add `extract Owned<char>, j;` to allow CN to "`attach`" this resource to the iterated `Owned` resource. CN issues a warning, because nothing is, in fact, extracted: we are using `extract` only for the "`reverse`" direction.

<span style="color:red">
BCP: That last bit is mysterious. 
</span>
<span style="color:red">
Dhruv: See long explanation and issue here: rems-project/cerberus#498 
</span>

### Exercises

**Init array reverse.** Verify the function `init_array_rev`, which has the same specification as `init_array2`, but initializes the array in decreasing index order (from right to left).

```c title="exercises/init_array_rev.c"
--8<--
exercises/init_array_rev.c
--8<--
```

<span style="color:red">
A potential case study (involving nested iteration):
    https://github.com/rems-project/cerberus/issues/848#issuecomment-2702085128
</span>
