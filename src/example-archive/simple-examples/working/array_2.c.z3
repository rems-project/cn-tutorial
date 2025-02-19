return code: 0
./src/example-archive/simple-examples/working/array_2.c:5:12: warning: 'each' expects a 'u64', but 'j' with type 'i32' was provided. This will become an error in the future.
      take arrayStart = each (i32 j; 0i32  <= j && j < size) {Owned(arr + j)};
           ^
./src/example-archive/simple-examples/working/array_2.c:10:12: warning: 'each' expects a 'u64', but 'j' with type 'i32' was provided. This will become an error in the future.
      take arrayEnd = each (i32 j; 0i32  <= j && j < size) {Owned(arr + j)};
           ^
other location (Cn__Compile.UsingLoads.handle.load)  warning: 'extract' expects a 'u64', but 'read_&off0' with type 'i32' was provided. This will become an error in the future.

[1/1]: array_2 -- pass
