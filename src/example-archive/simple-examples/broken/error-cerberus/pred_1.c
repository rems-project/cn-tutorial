// An example of defining a simple CN predicate. Broken as of 2024-7-4 thanks
// to a CN parsing issue. See: https://github.com/rems-project/cerberus/issues/266

/*@ 
predicate (i32) TestMemoryEqZero_1(pointer p) {
  take PVal = Owned<int>(p); 
  if (PVal == 0i32) {
    return 1i32; 
  } else {
    return 0i32; 
  }
}
@*/

void pred_1(int *p) 
/*@ requires 
      take PreP = Owned<int>(p); 
      PreP == 0i32; @*/
/*@ ensures 
      take TestP = TestMemoryEqZero_1(p); 
      TestP == 1i32; @*/
{ 
  ; 
}
