# Function Specifications

Function specifications define a contract for your C functions, capturing
assumptions about input parameters and the state of global variables when the
function is called as well as the effects the caller should expect on function
exit.

Function specs are placed between the function header and body.

```c
int f(int *p)
/*@
    // Function spec goes here.
@*/
{
    return *p;
}
```

Function statements can have the following clauses.

| Syntax | Explanation |
| ------ | ----------- |
| <p><code>requires<br/>&emsp;cond;<br/>&emsp;cond;</code></p> | One or more conditions the function assumes are true when called. |
| <p><code>ensures<br/>&emsp;cond;<br/>&emsp;cond;</code></p>  | One or more conditions the function ensures are true on exit. |
| <p><code>accesses<br/>&emsp;id1;<br/>&emsp;id2;</code></p> | Global variables the function uses. |
| `trusted;` | A special keyword telling CN _not_ to verify the function but instead to assume the specification is correct.  Use with caution. |
| <code>function id;</code> | Experimental feature.  Automatically derives a CN function (see Auxiliary Definitions) from the C function. |

## Requires and Ensures

These are the most common clauses of function specifications.  Together,
they define a formal contract that callers of your function can rely on.

These clauses contain lists of [conditions](conditions.md).
Here's an example.

```c
int f(int *p)
/*@
  requires
    // p is not NULL and can be read and written by this function.
    Owned(p);

  ensures
    // Ownership of p is returned to the caller.  p remains non-NULL
    // and can be read and written by the caller. 
    take v = Owned(p);

    // The value returned by this function is equal to the contents of p.
    return == v;
@*/
{
    return *p;
}
```

## Accesses

The `accesses` clause is syntactic sugar for requiring ownership of global
variables and ensuring the return of that ownership.

In other words, the following function specifications are equivalent.

```c
int glob = 0;

int f1()
/*@
  accesses glob;
@*/
{
    return glob;
}

int f2()
/*@
  requires
    take glob_in = Owned<int>(&glob);

  ensures
    take glob_out = Owned<int>(&glob);
@*/
{
    return glob;
}
```

## Trusted Functions

The `trusted` keyword tells CN to assume that the function satisfies its
specification, rather than trying to verify it.  This is useful for defining
the expected behavior of library functions when you don't have the source code.
And sometimes convincing the solver of the truth of your specification takes
more time than you currently have.

The `trusted` keyword is also dangerous, because your function may, in fact,
_not_ implement its spec.  CN will verify every function that calls it assuming
that the conditions it claims to ensure will hold, but that may not be the case
when you run your program, leading to bugs or security vulnerabilities.

!!! warning
    TODO: Explain how to use runtime specification testing to validate trusted
    specs.

Here are a few examples of how to use (and not use) the `trusted` keyword.

### Library Functions

CN relies on having access to source code, but that's not always possible.
Third-party libraries, for example, are often distributed as binaries and
header files.  In order for CN to verify code that calls such library
functions, it's often necessary to tell CN what effect the function has that
your code relies on – such as the memory it touches, and sometimes the values
it returns.

Here's an example.

```c
// Returns the value pointed to by p.
int library_function(int *p);
/*@
  spec library_function(pointer p);
  requires
    take p_in = Owned(p);
  ensures
    take p_out = Owned(p);
    return == p_out;
@*/

int inc(int *p)
/*@
  requires
    take p_in = Owned(p);

  ensures
    take p_out = Owned(p);
    return == p_in + 1;
@*/
{
    return library_function(p) + 1;
}
```

!!! info
    This example uses the `spec` keyword and the `pointer` type.  See
    [auxiliary-definitions](auxiliary-definitions/README.md) and
    [types.md](types.md) for more details.

In order to prove that `inc` returns the right value, along with ownership of
`p`, CN needs to know that `library_function` returns the value of `*p` as well
as ownership of `p`.

### The Consequences of Misplaced Trust

Here's an example of where using the `trusted` keyword can go wrong.  Consider
the following function and trusted specification.

```c
int whoops(int *p)
/*@
  trusted;

  requires
    take p_in = Owned(p);

  ensures
    take p_out = Owned(p);
    return == p_out;
@*/
{
    int x = *p;
    free(p);
    return x + 1;
}
```

See the problem?

The spec claims that it returns ownership of `p` to the caller, but in reality
it frees the memory instead.  If the caller uses `p`, it will result in
undefined behavior.  Similarly, the spec claims that the return value is `*p`,
but really it's a different value – `*p + 1`.

This mismatch can lead to bugs.  Worse, because CN is instructed to trust this
spec, it will happily use it to verify the caller and report that the caller is
verified to be correct.

In summary, use caution when using the `trusted` keyword.
