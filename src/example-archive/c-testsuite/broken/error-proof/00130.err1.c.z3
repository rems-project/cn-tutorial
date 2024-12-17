return code: 1
[1/1]: main -- fail
./src/example-archive/c-testsuite/broken/error-proof/00130.err1.c:10:2: error: Missing resource for writing
	arr[1][3] = 2;
	~~~~~~~~~~^~~ 
Resource needed: Block<char>(&(&(&(&&arr[(u64)0'i32])[(u64)1'i32])[(u64)0'i32])[(
                                                                                  u64
                                                                                )3'i32])
State file: file:///tmp/state__00130.err1.c__main.html
