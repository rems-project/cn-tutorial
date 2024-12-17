return code: 1
[1/1]: main -- fail
./src/example-archive/c-testsuite/broken/error-proof/00142.err1.c:16:2: error: Unprovable constraint
	return c;
	^~~~~~~~~ 
Constraint from ./src/example-archive/c-testsuite/broken/error-proof/00142.err1.c:14:13:
/*@ ensures return == 0i32; @*/
            ^~~~~~~~~~~~~~~ 
State file: file:///tmp/state__00142.err1.c__main.html
