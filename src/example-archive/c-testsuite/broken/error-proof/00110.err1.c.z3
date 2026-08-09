return code: 1
[1/1]: main -- fail
./src/example-archive/c-testsuite/broken/error-proof/00110.err1.c:9:2: error: Unprovable constraint
	return x;
	^~~~~~~~~ 
Constraint from ./src/example-archive/c-testsuite/broken/error-proof/00110.err1.c:7:13:
/*@ ensures return == 0i32; @*/
            ^~~~~~~~~~~~~~~ 
State file: file:///tmp/state__00110.err1.c__main.html
