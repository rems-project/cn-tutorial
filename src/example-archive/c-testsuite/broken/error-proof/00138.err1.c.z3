return code: 1
[1/1]: main -- fail
./src/example-archive/c-testsuite/broken/error-proof/00138.err1.c:16:10: error: Missing resource for reading
	return (a[1] == 'i') ? 0 : 1;
	        ^~~~ 
Resource needed: Owned<char>(&a_630[(u64)1'i32])
State file: file:///tmp/state__00138.err1.c__main.html
