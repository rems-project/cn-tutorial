return code: 0
./src/example-archive/dafny-tutorial/working/binary_search.c:10:12: warning: 'each' expects a 'u64', but 'j' with type 'i32' was provided. This will become an error in the future.
      take IndexPre = each (i32 j; 0i32 <= j && j < length)
           ^
./src/example-archive/dafny-tutorial/working/binary_search.c:13:12: warning: 'each' expects a 'u64', but 'j' with type 'i32' was provided. This will become an error in the future.
      take IndexPost = each (i32 j; 0i32 <= j && j < length)
           ^
./src/example-archive/dafny-tutorial/working/binary_search.c:28:14: warning: 'each' expects a 'u64', but 'j' with type 'i32' was provided. This will become an error in the future.
        take IndexInv = each (i32 j; 0i32 <= j && j < length)
             ^
./src/example-archive/dafny-tutorial/working/binary_search.c:28:14: warning: 'each' expects a 'u64', but 'j' with type 'i32' was provided. This will become an error in the future.
        take IndexInv = each (i32 j; 0i32 <= j && j < length)
             ^
other location (Cn__Compile.UsingLoads.handle.load)  warning: 'extract' expects a 'u64', but 'read_&mid0' with type 'i32' was provided. This will become an error in the future.

./src/example-archive/dafny-tutorial/working/binary_search.c:34:9: warning: nothing instantiated
    /*@ instantiate good<int>, mid;  @*/
        ^~~~~~~~~~~~~~~~~~~~~~~~~~~ 
[1/1]: binary_search -- pass
