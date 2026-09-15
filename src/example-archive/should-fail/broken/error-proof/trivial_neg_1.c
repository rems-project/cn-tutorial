// Negative test case: proof should fail 

// The specification has a false postcondition 
void trivial_neg_1() 
/*@ ensures false; @*/
{
  ; 
}

int main(void)
/*@ trusted; @*/
{
  trivial_neg_1();
}