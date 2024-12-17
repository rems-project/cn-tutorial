return code: 1
[1/3]: create_string -- fail
[2/3]: copy_to_global -- fail
[3/3]: main -- fail
./src/example-archive/Rust/broken/error-proof/00007-string-transfer-no-io.c:41:15: error: Unknown function 'malloc_proxy'
    char *s = malloc(20 * sizeof(char));  // Allocate memory for the string
              ^~~~~~ 
./src/example-archive/Rust/broken/error-proof/00007-string-transfer-no-io.c:51:31: error: Mismatched types.
    strncpy(global_string, s, sizeof(global_string) - 1);
                              ~~~~~~~~~~~~~~~~~~~~~~^~~ 
Expected value of type 'u64' but found value of type 'u32'
./src/example-archive/Rust/broken/error-proof/00007-string-transfer-no-io.c:62:5: error: Unknown function 'free_proxy'
    free(my_string);  // Explicitly free the memory allocated in create_string
    ^~~~ 
