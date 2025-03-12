// Negative test case: proof should fail 

// Precondition includes access to the resource RW(p), which is duplicated in
// the postcondition  
void ownership_neg_3(int *p) 
/*@ requires take P = RW(p); @*/
/*@ ensures 
      take P_ = RW(p); 
      take Q_ = RW(p); @*/
{
  ; 
}