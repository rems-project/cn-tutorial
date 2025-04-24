# Quick Reference

A quick reference for CN keywords, symbols, and operations.

## Keywords

The following table contains keywords that are reserved for use by the CN
specification language.

| Keyword | Description | See also |
| ------- | ----------- | -------- |
| `accesses` | List of global variables used by a function. | [Function specifications](../specifications/function-specifications.md) |
| `each` | Condition that ranges over a set of values. | [Conditions](../specifications/conditions.md) |
| `ensures` | List of conditions that should be true on function exit. | [Function specifications](../specifications/function-specifications.md) |
| `false` | Boolean false literal. | [Expressions](../specifications/expressions.md) |
| `function` | Reserved for future use. | |
| `good` | TODO | |
| `implies` | Logical implication, with `a implies b` equivalent to `-a || b`. | [Expressions](../specifications/expressions.md) |
| `inv` | List of loop invariant conditions. | [Loop invariants](../specifications/loop-invariants.md) |
| `let` | Variable assignment in conditions. | [Conditions](../specifications/conditions.md) |
| `requires` | List of conditions that should be true before calling a function. | [Function specifications](../specifications/function-specifications.md) |
| `return` | Special variable indicating the function return value in an `ensures` clause. | [Function specifications](../specifications/function-specifications.md) |
| `sizeof` | Built-in operation that returns the size of a given C type. | [Expressions](../specifications/expressions.md) |
| `take` | Condition for asserting that a resource predicate holds and binding its value. | [Conditions](../specifications/conditions.md) |
| `true` | Boolean true literal. | [Expressions](../specifications/expressions.md) |
| `trusted` | Prevents CN from attempting to verify a function. | [Function specifications](../specifications/function-specifications.md) |
| `unchanged` | TODO: is this a condition or expression? | |
| `W` | Resource predicate indicating an uninitialized, non-null memory object. | [Resource predicates](../specifications/resource-predicates.md) |
| `RW` | Resource predicate indicating an initialized, non-null memory object. | [Resource predicates](../specifications/resource-predicates.md) |
| `NULL` | The null value. | [Expressions](../specifications/expressions.md) |

## Operators

The following table contains a list of operators supported by CN.

| Operator | Example | Explanation |
| -------- | ------- | ----------- |
| `+` | `expr + expr` | Arithmetic/pointer addition |
| `-` | `expr - expr` | Arithmetic/pointer subtraction |
| `-` | `-expr`       | Arithmetic negation |
| `*` | `expr * expr` | Arithmetic multiplication |
| `*` | `*expr` | Pointer dereference |
| `/` | `expr / expr` | Arithmetic division |
| `%` | `expr % expr` | Arithmetic remainder |
| `,` | `expr, expr` | Argument separator |
| `&` | `&expr` | Pointer address of |
| `&` | `expr & expr` | Bitwise AND |
| `&&` | `expr && expr` | Logical AND |
| `|` | `expr | expr` | Bitwise OR |
| `||` | `expr || expr` | Logical OR |
| `~` | `~expr` | Bitwise negation |
| `>` | `expr > expr` | Greater than comparison |
| `>=` | `expr >= expr` | Greater than or equal to comparison |
| `<<` | `expr << expr` | *Bitwise shift left (not implemented)* |
| `>>` | `expr >> expr` | *Bitwise shift right (not implemented)* |
| `!` | `!expr` | Logical negation |
| `!=` | `expr != expr` | Nonequality comparison |
| `<` | `expr > expr` | Less than comparison |
| `<=` | `expr <= expr` | Less than or equal to comparison |
| `==` | `expr == expr` | Equality comparison |
| `.` | `expr.expr` | Struct field projection |
| `implies` | `expr implies expr` | Logical implication |
| `pow` | `pow(expr, expr)` | *Arithmetic exponentiation (not implemented)* |

## Symbols

CN defines a number of special constants for convenience in writing
expressions.

| Symbol | Example | Explanation |
| ------ | ------- | ----------- |
| `default<cntype>` | `default<struct foo>` | TODO |
| `MAX` | `MAXi8()` | Maximum value for each integer type |
| `MIN` | `MINi8()` | Minimum value for each integer type |

## Literal values

CN currently recognizes Boolean, pointer, and integer literals.  CN does not
recognize compound C literals, like string, array, and struct literals.

| Pattern | Example | Explanation |
| ------- | ------- | ----------- |
| `false` | | Boolean false literal |
| `true` | | Boolean true literal |
| `NULL` | | The null pointer literal |
| `<integer><cntype>` | `0i32` | Typed integer literal with CN type |
| `<integer>{U, UL, ULL, L, LL}` | `0ULL` | C typed integer literal |

