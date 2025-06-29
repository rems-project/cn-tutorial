return code: 1
[1/1]: main -- fail
./src/example-archive/c-testsuite/broken/error-proof/00117.err1.c:21:9: error: Missing resource for reading
	return x[1];
	       ^~~~ 
Resource needed: Owned<signed int>(&(&&x[(u64)0'i32])[(u64)1'i32])
State file: file:///tmp/state__00117.err1.c__main.html
