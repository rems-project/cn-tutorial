# Loop Invariants

Loop invariants describe facts about the loop that are _always_ true,
regardless of how many times it executes.  CN checks that loop invariants are
true before the loop executes and during every possible iteration, and then
uses them to prove things about the rest of the code downstream.

Loop invariants always start with the `inv` keyword.

| Syntax | Explanation |
| ------ | ----------- |
| <p><code>inv<br/>&emsp;condition;<br/>&emsp;condition;</code></p> | One or more conditions that are always true before, during, and after loop execution. |

!!! warning
    Loop invariants only work with `for` and `while` loops.  They are not
    implemented yet for `do-while` loops.

Here's an example.  Suppose we want to prove memory safety of an array search –
that is, verifying that we always index within the bounds of the array, and
that the returned index is either within the bounds of the array or `-1`,
indicating the searched-for element is not found.

```c linenums="1"
int find(int k, int arr[], int len)
/*@
  requires
    take arr_in = each (i32 j; 0i32 <= j && j < len) {
      RW(arr + j)
    };
    0i32 <= len;

  ensures
    take arr_out = each (i32 j; 0i32 <= j && j < len) {
      RW(arr + j)
    };
    0i32 <= return && return < len || return == -1i32;
@*/
{
  for (int i = 0; i < len; i++)
  /*@
    inv
      0i32 <= i && i <= len;

      {arr} unchanged;
      {len} unchanged;
      {k} unchanged;

      take arr_inv = each (i32 j; 0i32 <= j && j < len) {
        RW(arr + j)
      };
  @*/
  {
    /*@ focus RW<int>, i; @*/
    if (arr[i] == k)
    {
      return i;
    }
  }

  return -1;
}
```

The array invariant (lines 17 – 28) establishes a few facts:

* The index `i` is at least zero less than or equal to `len`.  Note the "or equal to" part – the invariant holds before, during, _and after_ the loop.  After the loop, `i == len`.
* `arr`, `len`, and `k` are not modified in the loop.
* Memory ownership is preserved throughout the loop.

Together, these facts let CN prove that the return value is either a valid
index in the array or `-1`.

!!! info
    You might wonder – can't CN figure out which variables are unchanged?
    
    We think so, and we're working to make that happen.  In the meantime,
    you'll need to indicate variables that are unchanged in the loop.
