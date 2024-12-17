return code: 0
./src/examples/add_two_array.c:3:19: warning: 'each' expects a 'u64', but 'k' with type 'i32' was provided. This will become an error in the future.
/*@ requires take A = each(i32 k; 0i32 <= k && k < n) { 
                  ^
./src/examples/add_two_array.c:8:18: warning: 'each' expects a 'u64', but 'k' with type 'i32' was provided. This will become an error in the future.
    ensures take A_post = each(i32 k; 0i32 <= k && k < n) { 
                 ^
other location (Cn__Compile.UsingLoads.handle.load)  warning: 'extract' expects a 'u64', but 'read_&i0' with type 'i32' was provided. This will become an error in the future.

other location (Cn__Compile.UsingLoads.handle.load)  warning: 'extract' expects a 'u64', but 'read_&j0' with type 'i32' was provided. This will become an error in the future.

[1/1]: array_read_two -- pass
