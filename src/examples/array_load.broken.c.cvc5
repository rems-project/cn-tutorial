return code: 1
./src/examples/array_load.broken.c:2:19: warning: 'each' expects a 'u64', but 'j' with type 'i32' was provided. This will become an error in the future.
/*@ requires take A = each(i32 j; 0i32 <= j && j < n) { 
                  ^
./src/examples/array_load.broken.c:5:18: warning: 'each' expects a 'u64', but 'j' with type 'i32' was provided. This will become an error in the future.
    ensures take A_post = each(i32 j; 0i32 <= j && j < n) { 
                 ^
[1/1]: read -- fail
./src/examples/array_load.broken.c:9:10: error: `&p[(u64)i]` out of bounds
  return p[i];
         ^~~~ 
(UB missing short message): UB_CERB004_unspecified__pointer_add
State file: file:///tmp/state__array_load.broken.c__read.html
