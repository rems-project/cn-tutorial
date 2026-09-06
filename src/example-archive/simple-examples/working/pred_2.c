// Examples encoding control-flow for predicates. These are a contrived to work
// around a CN parser issue. See https://github.com/rems-project/cerberus/issues/266 

// Variant 1 - this works: 
/*@ 
predicate (integer) TestMemoryEqZero_2_var1(pointer p) {
  take PVal = RW<int>(p); 
  let rval = test_if_zero(PVal); 
  return rval; 
}

function (integer) test_if_zero(integer x) {
  if (x == 0) {
    1
  } else { 
    0 
  }
}
@*/

void pred_2_var1(int *p) 
/*@ requires 
      take PreP = RW<int>(p); 
      PreP == 0;
    ensures 
      take TestP = TestMemoryEqZero_2_var1(p); 
      TestP == 1; @*/
{ 
  ; 
}

// Variant 2 - this works: 
/*@ 
predicate (integer) TestMemoryEqZero_2_Helper(pointer p, integer x) {
  if (x == 0) {
    return 1; 
  } else { 
    return 0; 
  }
}


predicate (integer) TestMemoryEqZero_2_var2(pointer p) {
  take PVal = RW<int>(p); 
  take rval = TestMemoryEqZero_2_Helper(p, PVal); 
  return rval; 
}
@*/

void pred_2_var2(int *p) 
/*@ requires 
      take PreP = RW<int>(p); 
      PreP == 0;
    ensures 
      take TestP = TestMemoryEqZero_2_var2(p); 
      TestP == 1; @*/
{ 
  ; 
}

// Variant 3 - this works: 
/*@ 
predicate (integer) TestMemoryEqZero_2_var3(pointer p) {
  take PVal = RW<int>(p); 
  let rval = (PVal == 0 ? 1 : 0); 
  return rval; 
}
@*/

void pred_2_var3(int *p) 
/*@ requires 
      take PreP = RW<int>(p); 
      PreP == 0;
    ensures 
      take TestP = TestMemoryEqZero_2_var3(p); 
      TestP == 1; @*/
{ 
  ; 
}

