// Negative test case: proof should fail 

// The precondition constraints i to be the minimum allowed value of an i32. The
// function decrements this value, which overflows the value and causes UB 
void overflow_neg_2(int i) 
/*@ requires i == MINi32(); @*/
{
  i = i - 1; 
}

int main(void)
/*@ trusted; @*/
{
  int x = -2147483648;
  overflow_neg_2(x);
}