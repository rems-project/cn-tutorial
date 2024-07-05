// Negative test case: proof should fail 

// The specification has a false postcondition 
void trivial_neg_1() 
/*@ ensures false; @*/
{
  ; 
}