// Negative test case: proof should fail 

// Precondition includes access to the resource Owned(p), which disappears in
// the postcondition 
void ownership_neg_1(int *p) 
/*@ requires take P = Owned(p); @*/
/*@ ensures true; @*/
{
  ; 
}