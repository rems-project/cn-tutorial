# Arrays and loops

Another common datatype in C is arrays. Reasoning about memory ownership for arrays is more difficult than for the datatypes we have seen so far, for two reasons: (1) C allows the programmer to access arrays using _computed pointers_, and (2) the size of an array does not need to be known as a constant at compile time.

To support reasoning about code manipulating arrays and computed pointers, CN has _iterated resources_. For instance, to specify ownership of an `unsigned` array with 10 cells starting at pointer `p`, CN uses the following iterated resource:

{{ todo("JWS: I think these should be `u64`s (per the warning),
but then the sizes `n` need to be cast to `u64` from `u32`
in the later example. Not sure what the cleanest route is here.")}}

```c
each (u32 i; i < 10u32)
{ RW<unsigned int>(array_shift<unsigned int>(p,i)) }
```

In detail, this can be read as follows:

- for each index `i` of CN type `u32`, …

- if `i` is between `0` and `10`, …

- assert ownership of a resource `RW<unsigned int>` …

- for cell `i` of the array with base-address `p`.

Here `array_shift<unsigned int>(p,i)` computes a pointer into the array at pointer `p`, appropriately offset for index `i`.

In general, the syntax of `each` is as follows:

```c
each (<type> <var>; <boolean expr>) { <expr> }
```

### First array example

Let’s see how this applies to a simple array-manipulating function. Function `read` takes three arguments: the base pointer `p` of an `unsigned int` array, the length `n` of the array, and an index `i` into the array; `read` then returns the value of the `i`-th array cell.

```c title="exercises/array_load.test.c"
--8<--
exercises/array_load.test.c
--8<--
```

The CN precondition requires

- ownership of the array on entry — one `RW<unsigned int>` resource for each array index between `0` and `n - 1` — and
- that `i` lies within the range of RW indices.

On exit the array ownership is returned again. The postcondition also asserts that the return value of the function is indeed equal to the value of the array at index `i`.

### Writing to arrays

Consider this next function `writei`, which sets the value of the `i`-th array cell to be `val`.

```c title="exercises/array_write.test.c"
--8<--
exercises/array_write.test.c
--8<--
```

The specification closely resembles that of `read`, except for the last line, which now asserts that `A_post[i]`, the value of the array _after_ the function executes at index `i`, is equal to `val`.

What if we additionally wanted to make assertions about values in the array _not_ being modified? In the prior `read` example, we could add
```c
A == A_post
```
to assert that the array before execution has the same values as the array after execution. In this `writei` example, we can replace the last line with
```c
A[i:v] == A_post
```
to assert that the array before execution, with index `i` updated to `v`, has the same values as the array after execution. Note that the update syntax can be sequenced, e.g., `A[i:v1][j:v2]`.

#### Exercises

_Exercise:_ Write a specification for `array_swap`, which swaps the values of two cells of an int array. Assume that `i` and `j` are different.

```c title="exercises/array_swap.c"
--8<-
exercises/array_swap.c
--8<--
```

### Iterated conditions

Suppose we are writing a function that returns the maximum value in an array. Informally, we would want a postcondition that asserts that the returned value is greater than or equal to _each_ value in the array. Formally, for an array `A` of length `n`, we use an _iterated condition_ to write

```c
each (u32 i; i < n)
{ return >= A[i] };
```

Then, together with our usual conditions about ownership, as well as a precondition that the array is non-empty, we have this specification:

```c
/*@ requires take A = each(u32 i; i < n)
                      { RW<unsigned int>(array_shift<unsigned int>(p,i)) };
             n > 0u32;
    ensures take A_post = each(u32 i; i < n)
                          { RW<unsigned int>(array_shift<unsigned int>(p,i)) };
            each (u32 i; i < n)
            { return >= A[i] };

@*/
```

We next test this specification on this implementation of `array_max`.

```c title="exercises/array_max.broken.c"
--8<--
exercises/array_max.broken.c
--8<--
```

If we run cn test, we get this error, and an associated counterexample

```
************************ Failed at *************************
function array_max, file ./array_max2.broken-exec.c, line 36
Load failed.
  ==> 0x122534a74[0] (0x122534a74) not owned
```

This "not owned" error suggests that we are trying to access a region of memory that we do not have ownership over — an index out-of-bounds issue, perhaps. Indeed, if we inspect our implementation, we realize that we need to fix the `i <= n` to `i < n`.


If we run `cn test` again, we now get

```
************************ Failed at *************************
function array_max, file ./array_max.broken-exec.c, line 117
original source location:
            each (u32 i; i < n)
            ^~~~~~~~~~~~~~~~~~~ array_max.broken.c:7:13-8:32

********************** Failing input ***********************

void* p0 = malloc(12);
*((unsigned int*)p0) = 18;
*((unsigned int*)((uintptr_t)p0 + 4)) = 0;
*((unsigned int*)((uintptr_t)p0 + 8)) = 17;
unsigned int* p = (unsigned int*)(p0);
unsigned int n = (unsigned int)(3);
array_max(p, n);

************************************************************

```

Examining the generated counterexample, we see that the elements of the array are `{18, 0, 17}`, so the first element is the maximum. And if we generate counterexamples a few more times, we see that this pattern persists. Inspecting our implementation a bit further, we find and fix another bug: in the first line, we should initialize `max` to be `p[0]`, not `0`.

(An additional debugging tip: if the generated counterexample arrays are too large, we can restrain them by adding a temporary precondition such as `n <= 3u32`, to force the array to be of length at most three, or some other suitable bound.)
{{ later("JWS: I personally found this a useful hack, but I don't
know if we want to advertise it as an officially sanctioned tip. (How
close are folks to adding shrinking?)") }}

Now, `cn test` will succeed!

#### Exercises

_Exercise:_ Write a specification for `array_add3`, which should add three to each array value. Your specification should succeed on this correct implementation, and fail when bugs are inserted (e.g., if four is added instead):

```c title="exercises/array_add3.test.c"
--8<--
exercises/array_add3.test.c
--8<--
```

_Exercise:_ Write a specification for `array_sort`, which should sort
an array into increasing order. Your specification should succeed on
this correct implementation below
(yes, [it's correct](https://arxiv.org/abs/2110.01111)), and fail
when bugs are inserted:

{{ later("JWS: One gnarly aspect of this is that you need to carefully
avoid the `i + 1` in `i + 1 < n` overflowing. The version I got to
work was to add a (seemingly redundant, but not actually) condition `i
< n`. Slight variations, such as to assume a non-empty array, seem to
make testing really really slow, and I'm not sure why. We should a)
figure out what's the most elegant solution and b) give a hint to that
effect.") }}

```c title="exercises/array_sort.test.c"
--8<--
exercises/array_sort.test.c
--8<--
```
