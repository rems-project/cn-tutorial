// Negative test case: proof should fail 

// The precondition constraints i to be the minimum allowed value of an i32. The
// function decrements this value, which overflows the value and causes UB 
void overflow_neg_2(int i) 
/*@ requires i == MINi32(); @*/
{
  i = i - 1; 
}