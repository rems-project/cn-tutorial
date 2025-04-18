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

Using the counterexample from [First Taste](./first-taste.md):

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

- Run `cn test` multiple times
- Note how it passes sometimes
- `--print-seed` and `--seed` to reproduce?
- Tests that sometimes pass and sometimes fail are known as "flaky tests"
- We can make our tests less flaky by removing the randomness and making a unit test.
  - Now we can be confident when re-running `cn test` that `'z'` is being included in our testing.
  - Maybe include in main PBT pages to demonstrate how to handle flaky PBT.
