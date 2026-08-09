# Arrays and Loops

In C programming, arrays are a fundamental data structure, but 
reasoning about their about their behavior can be challenging. 
This complexity arises from two primary factors:

1. Pointer Arithmetic: C allows direct manipulation of array elements 
  through pointers, which can lead to subtle bugs if not handled 
  carefully.
2. Dynamic Sizes: The size of an array isn't always known at compile 
  time.

{{ hidden("AZ: Replaced _computed pointers_ with pointer arithmetic
as it did not seem to be a standardized term.")}}

CN address these challenges via _iterated resources_. An 
_iterated resource_ is a way to express ownership over a sequence of 
memory locations, such as the elements of an array. This concept is 
crucial for reasoning about the safety and correctness of array 
manipulations.

### Iterated Resources: Array Ownership

Suppose you have an array of type `unsigned int` and length 10. To 
express that you own the entire array — i.e., that it’s safe to read 
from or write to any of its cells — you use an _iterated resource_. 
Let's say that the array starts at pointer `p`, then CN uses the 
following iterated resource:

{{ todo("JWS: I think these should be `u64`s (per the warning),
but then the sizes `n` need to be cast to `u64` from `u32`
in the later example. Not sure what the cleanest route is here.")}}

```c
each (u32 i; i < 10u32)
{ RW<unsigned int>(array_shift<unsigned int>(p,i)) }
```

This can be read as follows:

- for each index `i` of type `u32`, if `i` is between `0` and `10`, {{ todo("AZ: The upper limit should be 9 instead of 10.")}}
- assert ownership of a resource `RW<unsigned int>`
- for cell `i` of the array with base-address `p`.

Here `array_shift<unsigned int>(p,i)` computes a pointer into the array at pointer `p`, appropriately offset for index `i`. {{ todo("AZ: Should it be describes/specifies instead of computes?")}}

The general syntax of `each` is as follows:

```c
each (<type> <var>; <boolean expr>) { <expr> }
```

Where: {{ todo("AZ: Please review this for correctness.")}}

- `<type> <var>` introduces a variable `<var>` of type `<type>`,
- `<boolean expr>` is a condition that limits the range of `<var>`,
- `<expr>` is the resource expression that uses `<var>`.

This is CN’s way of writing a quantified ownership assertion — a loop 
over memory, but in the spec.
{{ todo("AZ: This might be a good place to add more context on `each` and when to reach out for it when writing CN specifications.")}}

### Reading From Arrays

Let’s see how this applies to a simple simple function that reads an 
element from an array. Function `read` takes three arguments: the 
base pointer `p` to an `unsigned int` array, the length `n` of the 
array, and an index `i` into the array; `read` then returns the value 
of the `i`-th array cell.

```c title="exercises/array_load.test.c"
--8<--
exercises/array_load.test.c
--8<--
```

In this CN specification, the precondition requires:  

- the ownership of the array on entry — one `RW<unsigned int>` resource for each array index between `0` and `n - 1`, and,
- that `i` lies within the range of RW indices.

On exit, the postcondition ensures that:  

- the array ownership is returned, and
- the return value of the function is equal to the value of the array 
  at index `i`.


### Writing to Arrays

Consider this next function `writei`, which sets the value of the `i`-th array cell to be `v`.

```c title="exercises/array_write.test.c"
--8<--
exercises/array_write.test.c
--8<--
```

Here, the specification closely resembles that of `read`, except for 
the last line, which now asserts that `A_post[i] == v`, i.e. - the 
value of the array _after_ the function executes at index `i`, should
be equal to `v`.

What if we additionally wanted to make assertions about values in the 
array _not_ being modified? In the prior `read` example, we could add
```c
A == A_post
```
to assert that the array before execution has the same values as the array after execution. In this `writei` example, we can replace the last line with
{{ later("AZ: Adding the spec that read function leaves the array 
unchanged in the previous example will make the presentation more
 linear")}}
```c
A[i:v] == A_post
```
to assert that the array before execution, with index `i` updated to `v`, has the same values as the array after execution. Note that the update syntax can be sequenced, e.g., `A[i:v1][j:v2]`.

### Exercises

_Exercise:_ Swapping Array Elements.  
Write a specification for `array_swap`, a function which swaps the 
values of two cells of an int array. Assume that `i != j`.

```c title="exercises/array_swap.c"
--8<-
exercises/array_swap.c
--8<--
```

### Iterated Conditions

Ownership is one part of the story — correctness is the other. Suppose 
we are writing a function `array_max` that returns the maximum value 
in an array. We would want the postcondition to assert that the 
returned value is greater than or equal to every element in the array.
For an array `A` of length `n`, here is how you do that with an 
 _iterated condition_:

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

Next, we would like to test this specification on the below 
implementation of `array_max`.

```c title="exercises/array_max.broken.c"
--8<--
exercises/array_max.broken.c
--8<--
```

If we run `cn test`, we get the below error and an associated 
counterexample.

```
************************ Failed at *************************
function array_max, file ./array_max2.broken-exec.c, line 36
Load failed.
  ==> 0x122534a74[0] (0x122534a74) not owned
```

This "not owned" error suggests that we are trying to access a region of memory that we do not have ownership over — an index out-of-bounds issue, perhaps. Indeed, if we inspect our implementation, we realize that we need to fix the `i <= n` to `i < n`.


If we run `cn test` on the fixed version, it still fails with the 
below message.

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

Examining the generated counterexample, we see that the elements of 
the array are `{18, 0, 17}`.  In this case, the first element, 18, is 
clearly the maximum. However, our function violates the postcondition.
{{ todo("AZ: From the error message, it is not clear to me that the 
postcondition is violated. There are multiple usages of each in the 
spec and it is not clear which one is the source of error. Neither
does the CounterExample talk about the return value (max). 
Suggestion: Adding line numbers in the listing might help here since 
the error message seems to produce a line number which might 
disambiguate which each the error is referring to. ")}}
If we run the test multiple times, we consistently see similar 
patterns in the counterexamples - arrays where the first element holds
the maximum value, yet the function fails to return it. This suggests 
a deeper issue with how the initial value of max is chosen. Looking 
more closely at the implementation, we realize that the problem lies 
in the line that initializes `max` as `int max = 0;`. We should have
initialized `max` to be `p[0]`, and not `0`.

!!! tip
    If the generated counterexample arrays are too large, try 
    temporarily restricting their length `n` to debug more easily.
    For example, we can restrain them to a small length of 3 by adding
    a precondition such as `n <= 3u32`.

{{ later("JWS: I personally found this a useful hack, but I don't
know if we want to advertise it as an officially sanctioned tip. (How
close are folks to adding shrinking?)") }}

Now, `cn test` will succeed!

### Exercises

_Exercise:_ Adding to Each Element  
Write a specification for `array_add3`, which adds `3` to each array 
value. Your specification should succeed on this correct 
implementation, and fail when bugs are inserted (e.g., if four is 
added instead):

```c title="exercises/array_add3.test.c"
--8<--
exercises/array_add3.test.c
--8<--
```

_Exercise:_ Sorting an Array  
Write a specification for `array_sort`, which sorts an array into 
increasing order. Your specification should succeed on
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
