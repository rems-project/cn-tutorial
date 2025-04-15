return code: 0
./src/examples/swap_array.c:3:19: warning: 'each' expects a 'u64', but 'k' with type 'i32' was provided. This will become an error in the future.
/*@ requires take a1 = each(i32 k; 0i32 <= k && k < n) { Owned<int>(array_shift<int>(p,k)) };
                  ^
./src/examples/swap_array.c:7:18: warning: 'each' expects a 'u64', but 'k' with type 'i32' was provided. This will become an error in the future.
    ensures take a2 = each(i32 k; 0i32 <= k && k < n) { Owned<int>(array_shift<int>(p,k)) };
                 ^
other location (Cn__Compile.UsingLoads.handle.load)  warning: 'extract' expects a 'u64', but 'read_&i0' with type 'i32' was provided. This will become an error in the future.

other location (Cn__Compile.UsingLoads.handle.load)  warning: 'extract' expects a 'u64', but 'read_&j0' with type 'i32' was provided. This will become an error in the future.

[1/1]: swap_array -- pass
