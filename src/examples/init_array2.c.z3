return code: 0
./src/examples/init_array2.c:2:19: warning: 'each' expects a 'u64', but 'i' with type 'u32' was provided. This will become an error in the future.
/*@ requires take A = each(u32 i; i < n) { 
                  ^
./src/examples/init_array2.c:4:19: warning: 'each' expects a 'u64', but 'i' with type 'u32' was provided. This will become an error in the future.
    ensures  take A_post = each(u32 i; i < n) { 
                  ^
./src/examples/init_array2.c:11:16: warning: 'each' expects a 'u64', but 'i' with type 'u32' was provided. This will become an error in the future.
  /*@ inv take Al = each(u32 i; i < j) { 
               ^
./src/examples/init_array2.c:13:16: warning: 'each' expects a 'u64', but 'i' with type 'u32' was provided. This will become an error in the future.
          take Ar = each(u32 i; j <= i && i < n) { 
               ^
./src/examples/init_array2.c:11:16: warning: 'each' expects a 'u64', but 'i' with type 'u32' was provided. This will become an error in the future.
  /*@ inv take Al = each(u32 i; i < j) { 
               ^
./src/examples/init_array2.c:13:16: warning: 'each' expects a 'u64', but 'i' with type 'u32' was provided. This will become an error in the future.
          take Ar = each(u32 i; j <= i && i < n) { 
               ^
other location (Cn__Compile.UsingLoads.handle.load)  warning: 'extract' expects a 'u64', but 'read_&j0' with type 'u32' was provided. This will become an error in the future.

other location (Cn__Compile.UsingLoads.handle.load)  warning: 'extract' expects a 'u64', but 'read_&j1' with type 'u32' was provided. This will become an error in the future.

./src/examples/init_array2.c:22:9: warning: extract: index added, no resources (yet) extracted.
    /*@ extract Owned<char>, j; @*/
        ^~~~~~~~~~~~~~~~~~~~~~~ 
[1/1]: init_array2 -- pass
