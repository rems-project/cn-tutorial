// Examples encoding control-flow for predicates. These are a contrived to work
// around a CN parser issue. See https://github.com/rems-project/cerberus/issues/266 

// Variant 1 - this works: 
/*@ 
predicate (i32) TestMemoryEqZero_2_var1(pointer p) {
  take PVal = RW<int>(p); 
  let rval = test_if_zero(PVal); 
  return rval; 
}

function (i32) test_if_zero(i32 x) {
  if (x == 0i32) {
    1i32
  } else { 
    0i32 
  }
}
@*/

void pred_2_var1(int *p) 
/*@ requires 
      take PreP = RW<int>(p); 
      PreP == 0i32;
    ensures 
      take TestP = TestMemoryEqZero_2_var1(p); 
      TestP == 1i32; @*/
{ 
  ; 
}

// Variant 2 - this works: 
/*@ 
predicate (i32) TestMemoryEqZero_2_Helper(pointer p, i32 x) {
  if (x == 0i32) {
    return 1i32; 
  } else { 
    return 0i32; 
  }
}


predicate (i32) TestMemoryEqZero_2_var2(pointer p) {
  take PVal = RW<int>(p); 
  take rval = TestMemoryEqZero_2_Helper(p, PVal); 
  return rval; 
}
@*/

void pred_2_var2(int *p) 
/*@ requires 
      take PreP = RW<int>(p); 
      PreP == 0i32;
    ensures 
      take TestP = TestMemoryEqZero_2_var2(p); 
      TestP == 1i32; @*/
{ 
  ; 
}

// Variant 3 - this works: 
/*@ 
predicate (i32) TestMemoryEqZero_2_var3(pointer p) {
  take PVal = RW<int>(p); 
  let rval = (PVal == 0i32 ? 1i32 : 0i32); 
  return rval; 
}
@*/

void pred_2_var3(int *p) 
/*@ requires 
      take PreP = RW<int>(p); 
      PreP == 0i32;
    ensures 
      take TestP = TestMemoryEqZero_2_var3(p); 
      TestP == 1i32; @*/
{ 
  ; 
}

