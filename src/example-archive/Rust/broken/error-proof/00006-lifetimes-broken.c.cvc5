return code: 1
./src/example-archive/Rust/broken/error-proof/00006-lifetimes-broken.c:37:15: warning: CN pointer equality is not the same as C's (will not warn again). Please use `ptr_eq` or `is_null` (maybe `addr_eq`).
              return == input; 
              ~~~~~~~^~~~~~~~ 
[1/2]: borrow -- pass
[2/2]: main -- fail
./src/example-archive/Rust/broken/error-proof/00006-lifetimes-broken.c:51:2: error: Missing resource for writing
	global_int = *r;
	~~~~~~~~~~~^~~~ 
Resource needed: Block<signed int>(&global_int)
State file: file:///tmp/state__00006-lifetimes-broken.c__main.html
