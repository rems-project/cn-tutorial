# Conditions

Conditions are used in [function specifications](function-specifications.md)
and [loop invariants](loop-invariants.md).  They represent facts about your
program that CN attempts to verify.

## Logical Conditions

Logical conditions come in two forms – simple Boolean-typed
[expressions](expressions.md), and Boolean-typed expressions that range
over a set of values, like the contents of an array.

| Condition | Syntax | Example |
| --------- | ------ | ------- |
| Single Boolean-typed expression | <code>&#x3C;expr></code></td><td><code>v == 1</code> |
| Iterated condition | <code>each (&#x3C;type> &#x3C;id>; &#x3C;expr>)<br/>{<br/>&emsp;&#x3C;expr><br/>}</code> | <code>each (u32 i; 0u32 &#x3C;= i &#x26;&#x26; i &#x3C; 10u32)<br/>{<br/>&emsp;0i32 &#x3C;= v_map[i]<br/>}</code> |

!!! info
    The example of an iterated condition uses the built-in `map` type.  See
    [built-in data structures](expressions.md#built-in-data-structures) for
    more details.

## Resource Conditions

Resource conditions mirror logical conditions in having simple and iterative
forms, with a key difference – they establish ownership of blocks of memory and
also return their contents.

| Condition | Syntax | Example |
| --------- | ------ | ------- |
| Single resource condition | `take <id> = <resource-predicate>` | `take v = Owned(p)` |
| Iterated resource condition | <p><code>take &#x3C;id> = each (&#x3C;type> &#x3C;id>; &#x3C;expr>)</code><br><code>{</code><br>  <code>&emsp;&#x3C;resource-predicate></code><br><code>}</code></p> | <p><code>take vs = each (u32 i; 0u32 &#x3C;= i &#x26;&#x26; i &#x3C; 10i32)</code><br><code>{</code><br>  <code>&emsp;Owned(p + i)</code><br><code>}</code></p> |

!!! info
    See [resource predicates](resource-predicates.md) for more
    information on the different kinds of resource predicates that can appear
    in resource conditions.

Here's an example that adds a number to each element in a list.  It uses
logical and resource conditions.

```c
void add_all(int *p, int arr[], int len)
/*@
  requires
    0i32 <= len;
    take v_in = Owned(p);
    take arr_in = each (i32 j; 0i32 <= j && j < len) {
      Owned(arr + j)
    };
    
  ensures
    take v_out = Owned(p);
    take arr_out = each (i32 j; 0i32 <= j && j < len) {
      Owned(arr + j)
    };
    each (i32 j; 0i32 <= j && j < len) {
      arr_out[j] = arr_in[j] + v_in;
    }
@*/
{
  for (int i = 0; i < len; i++)
  {
    arr[i] = *p;
  }
}
```

!!! warning
	TODO: This example does not, in fact, verify.

## Let Bindings

For convenience, you can also assign names to expressions for use in future expressions.

| Condition | Syntax | Example |
| --------- | ------ | ------- |
| Let binding | `let <id> = <expr>;` | `let tmp = 1 + 2;`  |
