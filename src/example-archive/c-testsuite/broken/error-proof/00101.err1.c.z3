return code: 1
[1/1]: main -- fail
./src/example-archive/c-testsuite/broken/error-proof/00101.err1.c:12:3: error: Unprovable constraint
  return c;
  ^~~~~~~~~ 
Constraint from ./src/example-archive/c-testsuite/broken/error-proof/00101.err1.c:5:13:
/*@ ensures return == 0i32; @*/
            ^~~~~~~~~~~~~~~ 
State file: file:///tmp/state__00101.err1.c__main.html
