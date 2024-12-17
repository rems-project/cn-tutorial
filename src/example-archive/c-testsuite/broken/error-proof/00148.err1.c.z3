return code: 1
[1/1]: main -- fail
./src/example-archive/c-testsuite/broken/error-proof/00148.err1.c:8:5: error: Pointer `&(&&arr[(u64)0'i32])[(u64)0'i32]` needs to be live for member shift
	if(arr[0].a != 1)
	   ~~~~~~^~ 
Need an Alloc or Owned in context with same allocation id
