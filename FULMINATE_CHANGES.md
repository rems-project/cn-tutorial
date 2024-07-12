# Changes for Fulminate Runtime test
-----

1. All files have `trusted` `main` functions.
2. All files still pass verification on CN proof mode.
3. Multi-file examples with struct declarations in them have been pre-processed and collapsed into to a single-file (a work-around).
4. Allocation and free functions \emph`remain` monomorphised but are implemented using Fulminate instrumented allocation and freeing rather than left as stubs.
5. (We do not quite support malloc/free because the CN specification lanaguage does have not the required polymorphism).
6. isomorphic single-constructor datatypes replaced anonymous records in specifications.
7. Guards for `each` expressions had lower bounds added (their indices are unsigned so for proof they only had upper bounds).
8. `ty x = e;` declarations before `while` loops were split up into two lines `ty x; x = e;` as a code-injection work-around.
