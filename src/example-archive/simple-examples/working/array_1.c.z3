return code: 0
./src/example-archive/simple-examples/working/array_1.c:5:12: warning: 'each' expects a 'u64', but 'j' with type 'i32' was provided. This will become an error in the future.
      take arrayStart = each (i32 j; 0i32 <= j && j < size) {Owned(arr + j)}; 
           ^
./src/example-archive/simple-examples/working/array_1.c:8:18: warning: 'each' expects a 'u64', but 'j' with type 'i32' was provided. This will become an error in the future.
/*@ ensures take arrayEnd = each (i32 j; 0i32 <= j && j < size) {Owned(arr + j)}; @*/
                 ^
other location (Cn__Compile.UsingLoads.handle.load)  warning: 'extract' expects a 'u64', but 'read_&i0' with type 'i32' was provided. This will become an error in the future.

[1/1]: array_1 -- pass
