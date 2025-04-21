# Unit testing (optional)

<!-- ## Reusing existing testing

(We currently go straight to PBT, because unit testing might be
integrated with build systems, unit testing infrastructure, etc., so
more complicated to set up.  Hard to predict exactly how this will
look as we scale.)

Fulminate, `cn instrument --run` -->

## Using unit testing with `cn test`

While the automatic testing provided by `cn test` is great,
sometimes one might want to test specific inputs to a function.

Two reasons would be regression testing and fixing flaky tests.

### Regression testing

Consider the `min3` example from [First Taste](./first-taste.md).
Suppose we fix the bug, but want to prevent a later regression.

We can define a new function that will test the previous counterexample:

{{ todo("""ZKA:
    I should add a compiler flag `__CN_TESTING`, which is true when running with `cn test`.
    Then we can put unit tests like this inside an `#ifdef`.
    Should also look into supporting user assertions (via a user-available library).""")
}}

```c
void test_min3() {
    min3(10, 2, 14);
}
```

Running `cn test` will run `test_min3`.

- an exercise to find a bug in a variant of min3
- couple more (similar, optional) exercises

### Fixing flaky tests

Due to `cn test` randomizing inputs, its possible that a failing input can be found on some runs, but not on others.

```c
void capitalize(char *str)
/*@
    requires take StrP = Owned<char>(str);
                  StrP >= 97u8 && StrP <= 122u8;
    ensures take StrP_post = Owned<char>(str);
                  StrP_post == StrP - 32u8;
    
@*/
{
    if(str != 0 && *str != 0 && *str >= 'a' && *str <= 'y') {
        *str -= 0x20;
    }
}
```

1. Run `cn test` multiple times
    1. Note how it passes sometimes
    2. Tests that sometimes pass and sometimes fail are known as "flaky tests"

2. `--print-seed` and `--seed` to reproduce?
    1. However, depends on the full testing workflow (functions under test, order tested)
    2. Could be better via per-input seeds...

3. A more robust solution for making our tests less flaky would be to add a unit test.
    1. Now we can be confident that, when re-running `cn test`, `'z'` is being tested.
