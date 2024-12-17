return code: 1
[1/1]: ownership_neg_2 -- fail
./src/example-archive/should-fail/broken/error-proof/ownership_neg_2.c:5:1: error: Missing resource for returning
void ownership_neg_2(int *p) 
~~~~~^~~~~~~~~~~~~~~~~~~~~~~~ 
Resource needed: Owned<signed int>(p)
      ./src/example-archive/should-fail/broken/error-proof/ownership_neg_2.c:7:18: (arg P_)
State file: file:///tmp/state__ownership_neg_2.c__ownership_neg_2.html
