# A first taste of verification

## Verifying `min3`

Property-based testing is great for increasing our confidence that
the function satisfies its specification, but we might also want
to _verify_ this formally. Run `cn verify <filename>` on the buggy
version to produce this output:

```
[1/1]: min3 -- fail
min3.c:11:9: error: Unprovable constraint
        return x;
        ^~~~~~~~~
Constraint from min3.c:2:13:
/*@ ensures return <= x
            ^~~~~~~~~~~
State file: file:///var/folders/_5/81fbkyvn3n5dsm34qw2zpr7w0000gn/T/state__min3.c__min3.html
```

And on the fixed version to produce this output:
```
[1/1]: min3 -- pass
```

Whereas `cn test` treats the function body as a black box, `cn
verify` analyzes it directly, examining all possible paths through
the code until it either succeeds in constructing a formal proof
that the function satisfies the specification, or it encounters a
constraint that cannot be satisfied.

{{ later("What else do we need to talk about in this introductory
section??") }}
