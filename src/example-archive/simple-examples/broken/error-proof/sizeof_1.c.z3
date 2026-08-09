return code: 1
[1/1]: main -- fail
./src/example-archive/simple-examples/broken/error-proof/sizeof_1.c:10:14: error: Mismatched types.
	int size2 = sizeof(int) + 1; // <- fails 
	            ~~~~~~~~~~~~^~~ 
Expected value of type 'u64' but found value of type 'u32'
