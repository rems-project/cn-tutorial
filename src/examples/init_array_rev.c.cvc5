return code: 0
./src/examples/init_array_rev.c:2:19: warning: 'each' expects a 'u64', but 'i' with type 'u32' was provided. This will become an error in the future.
/*@ requires take A = each(u32 i; i < n) { 
                  ^
./src/examples/init_array_rev.c:5:19: warning: 'each' expects a 'u64', but 'i' with type 'u32' was provided. This will become an error in the future.
    ensures  take A_post = each(u32 i; i < n) { 
                  ^
./src/examples/init_array_rev.c:12:16: warning: 'each' expects a 'u64', but 'i' with type 'u32' was provided. This will become an error in the future.
  /*@ inv take Al = each(u32 i; i < n-j) { 
               ^
./src/examples/init_array_rev.c:14:16: warning: 'each' expects a 'u64', but 'i' with type 'u32' was provided. This will become an error in the future.
          take Ar = each(u32 i; n-j <= i && i < n) { 
               ^
./src/examples/init_array_rev.c:12:16: warning: 'each' expects a 'u64', but 'i' with type 'u32' was provided. This will become an error in the future.
  /*@ inv take Al = each(u32 i; i < n-j) { 
               ^
./src/examples/init_array_rev.c:14:16: warning: 'each' expects a 'u64', but 'i' with type 'u32' was provided. This will become an error in the future.
          take Ar = each(u32 i; n-j <= i && i < n) { 
               ^
./src/examples/init_array_rev.c:22:30: warning: 'extract' expects a 'u64', but 'read_&n0
- (read_&j0 + 1'u32)' with type 'u32' was provided. This will become an error in the future.
    /*@ extract Block<char>, n-(j+1u32); @*/
                             ~^~~~~~~~~ 
./src/examples/init_array_rev.c:23:30: warning: 'extract' expects a 'u64', but 'read_&n1
- (read_&j1 + 1'u32)' with type 'u32' was provided. This will become an error in the future.
    /*@ extract Owned<char>, n-(j+1u32); @*/
                             ~^~~~~~~~~ 
./src/examples/init_array_rev.c:23:9: warning: extract: index added, no resources (yet) extracted.
    /*@ extract Owned<char>, n-(j+1u32); @*/
        ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ 
[1/1]: init_array_rev -- pass
