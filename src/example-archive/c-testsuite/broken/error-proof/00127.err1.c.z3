return code: 1
[1/1]: main -- fail
./src/example-archive/c-testsuite/broken/error-proof/00127.err1.c:14:5: error: Unprovable constraint
				return 1;
				^~~~~~~~~ 
Constraint from ./src/example-archive/c-testsuite/broken/error-proof/00127.err1.c:6:13:
/*@ ensures return == 0i32; @*/
            ^~~~~~~~~~~~~~~ 
State file: file:///tmp/state__00127.err1.c__main.html
