return code: 1
[1/1]: pointerdec_crash_3 -- fail
./src/example-archive/simple-examples/broken/error-proof/pointer_dec3.c:8:3: error: Missing resource for reading
  *(--p); 
  ^~~~~~ 
Resource needed: Owned<signed int>(&(&&arr[1'u64])[(u64)(0'i32 - 1'i32)])
State file: file:///tmp/state__pointer_dec3.c__pointerdec_crash_3.html
