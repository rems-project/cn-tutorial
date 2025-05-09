return code: 1
[1/1]: incr -- fail
./src/examples/slf0_incr.broken.c:8:11: error: Missing resource for reading
  int n = *p;
          ^~ 
Resource needed: Owned<signed int>(p)
State file: file:///tmp/state__slf0_incr.broken.c__incr.html
