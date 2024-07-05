// Negative test case: proof should fail 

// Precondition takes ownership of no resources, but then the postcondition
// claims ownership of Owned(p)  
void ownership_neg_2(int *p) 
/*@ requires true; @*/
/*@ ensures take P_ = Owned(p); @*/
{
  ; 
}