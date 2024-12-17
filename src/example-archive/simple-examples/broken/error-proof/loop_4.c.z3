return code: 1
[1/3]: loop_4 -- fail
[2/3]: loop_4_unrolled -- pass
[3/3]: loop_4_with_redundant_write -- pass
./src/example-archive/simple-examples/broken/error-proof/loop_4.c:11:3: error: Missing resource for loop
  while (i < 1) 
  ^~~~~~~~~~~~~~ 
Resource needed: Owned<signed int>(&t)
      ./src/example-archive/simple-examples/broken/error-proof/loop_4.c:11:3: (arg O_t0)
State file: file:///tmp/state__loop_4.c__loop_4.html
