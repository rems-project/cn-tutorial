return code: 0
./src/example-archive/simple-examples/working/array_3.c:8:12: warning: 'each' expects a 'u64', but 'j' with type 'i32' was provided. This will become an error in the future.
      take arrayStart = each (i32 j; 0i32 <= j && j < n) {Owned<int>(arr + j)}; @*/
           ^
./src/example-archive/simple-examples/working/array_3.c:10:12: warning: 'each' expects a 'u64', but 'j' with type 'i32' was provided. This will become an error in the future.
      take arrayEnd = each (i32 j; 0i32 <= j && j < n) {Owned<int>(arr + j)};
           ^
./src/example-archive/simple-examples/working/array_3.c:19:16: warning: 'each' expects a 'u64', but 'j' with type 'i32' was provided. This will become an error in the future.
          take arrayInv = each (i32 j; 0i32 <= j && j < n) {Owned<int>(arr + j)};
               ^
./src/example-archive/simple-examples/working/array_3.c:19:16: warning: 'each' expects a 'u64', but 'j' with type 'i32' was provided. This will become an error in the future.
          take arrayInv = each (i32 j; 0i32 <= j && j < n) {Owned<int>(arr + j)};
               ^
other location (Cn__Compile.UsingLoads.handle.load)  warning: 'extract' expects a 'u64', but 'read_&i0' with type 'i32' was provided. This will become an error in the future.

[1/1]: array_3 -- pass
