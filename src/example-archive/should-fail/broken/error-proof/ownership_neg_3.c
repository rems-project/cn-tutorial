// Negative test case: proof should fail 

// Precondition includes access to the resource Owned(p), which is duplicated in
// the postcondition  
void ownership_neg_3(int *p) 
/*@ requires take P = Owned(p); @*/
/*@ ensures 
      take P_ = Owned(p); 
      take Q_ = Owned(p); @*/
{
  ; 
}