return code: 1
./src/example-archive/Rust/broken/error-proof/00004-simple-lifetimes.c:35:15: warning: CN pointer equality is not the same as C's (will not warn again). Please use `ptr_eq` or `is_null` (maybe `addr_eq`).
              return == input; 
              ~~~~~~~^~~~~~~~ 
[1/2]: borrow -- pass
[2/2]: main -- fail
./src/example-archive/Rust/broken/error-proof/00004-simple-lifetimes.c:44:15: error: Missing resource for reading
    int ret = *r; // Safe to use 'r' here, as 'x' is still in scope
              ^~ 
Resource needed: Owned<signed int>(call_borrow0.return)
State file: file:///tmp/state__00004-simple-lifetimes.c__main.html
