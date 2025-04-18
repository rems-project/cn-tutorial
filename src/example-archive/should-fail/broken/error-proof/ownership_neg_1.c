// Negative test case: proof should fail 

// Precondition includes access to the resource RW(p), which disappears in
// the postcondition 
void ownership_neg_1(int *p) 
/*@ requires take P = RW(p); @*/
/*@ ensures true; @*/
{
  ; 
}