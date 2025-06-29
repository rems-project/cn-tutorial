return code: 0
./src/example-archive/dafny-tutorial/working/linear_search.c:6:12: warning: 'each' expects a 'u64', but 'j' with type 'i32' was provided. This will become an error in the future.
      take IndexPre = each (i32 j; 0i32 <= j && j < length)
           ^
./src/example-archive/dafny-tutorial/working/linear_search.c:9:12: warning: 'each' expects a 'u64', but 'j' with type 'i32' was provided. This will become an error in the future.
      take IndexPost = each (i32 j; 0i32 <= j && j < length)
           ^
./src/example-archive/dafny-tutorial/working/linear_search.c:23:14: warning: 'each' expects a 'u64', but 'j' with type 'i32' was provided. This will become an error in the future.
        take IndexInv = each (i32 j; 0i32 <= j && j < length)
             ^
./src/example-archive/dafny-tutorial/working/linear_search.c:23:14: warning: 'each' expects a 'u64', but 'j' with type 'i32' was provided. This will become an error in the future.
        take IndexInv = each (i32 j; 0i32 <= j && j < length)
             ^
other location (Cn__Compile.UsingLoads.handle.load)  warning: 'extract' expects a 'u64', but 'read_&idx0' with type 'i32' was provided. This will become an error in the future.

[1/1]: linear_search -- pass
