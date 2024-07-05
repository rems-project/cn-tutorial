// Negative test case: proof should fail 

// The precondition constraints i to be the maximum allowed value of an i32. The
// function increments this value, which overflows the value and causes UB 
void overflow_neg_1(int i) 
/*@ requires i == MAXi32(); @*/
{
  i = i + 1; 
}
