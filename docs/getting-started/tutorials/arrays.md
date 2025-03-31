# Arrays and Loops

Another common datatype in C is arrays. Reasoning about memory ownership for arrays is more difficult than for the datatypes we have seen so far, for two reasons: (1) C allows the programmer to access arrays using _computed pointers_, and (2) the size of an array does not need to be known as a constant at compile time.

To support reasoning about code manipulating arrays and computed pointers, CN has _iterated resources_. For instance, to specify ownership of an `unsigned` array with 10 cells starting at pointer `p`, CN uses the following iterated resource:

```c
each (u32 i; i < 10i32)
{ RW<unsigned int>(array_shift<unsigned int>(p,i)) }
```

In detail, this can be read as follows:

- for each index `i` of CN type `u32`, …

- if `i` is between `0` and `10`, …

- assert ownership of a resource `RW<unsigned int>` …

- for cell `i` of the array with base-address `p`.

Here `array_shift<unsigned int>(p,i)` computes a pointer into the array at pointer `p`, appropriately offset for index `i`.

<!--I think this part seems not worth including relative to its complexity-->
<!-- In general, iterated resource specifications take the form

```c
each (BT Q; GUARD) { RESOURCE }
```

comprising three parts:

- `BT Q`, for some CN type `BT` and name `Q`, introduces the quantifier `Q` of basetype `BT`, which is bound in `GUARD` and `RESOURCE`;

<span style="color:red"> BCP: What is a CN type?  What is a basetype?
</span>


- `GUARD` is a boolean-typed expression delimiting the instances of `Q` for which ownership is asserted; and

- `RESOURCE` is any non-iterated CN resource. -->

### First array example

Let’s see how this applies to a simple array-manipulating function. Function `read` takes three arguments: the base pointer `p` of an `unsigned int` array, the length `n` of the array, and an index `i` into the array; `read` then returns the value of the `i`-th array cell.

```c title="exercises/array_load.test.c"
--8<--
exercises/array_load.test.c
--8<--
```

The CN precondition requires

- ownership of the array on entry — one `RW<unsigned int>` resource for each array index between `0` and `n` — and
- that `i` lies within the range of RW indices.

On exit the array ownership is returned again. The postcondition also asserts that the return value of the function is indeed equal to the value of the array at index `i`.

<span style="color:red"> BCP: Do several more
examples (e.g., maybe working up to sorting?).
</span>
<span style="color:red">
JWS: I don't actually know how something like sorting can be specified in CN. Any pointers?
</span>
<span style="color:red"> BCP: Good question.  Let's ask on Mattermost.
</span>
