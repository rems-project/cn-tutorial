// Negative test case: proof should fail 

// The specification claims the function returns a non-zero value, but the
// implementation returns zero.
int arith_neg_1() 
/*@ ensures return != 0i32; @*/
{
  return 0; 
}