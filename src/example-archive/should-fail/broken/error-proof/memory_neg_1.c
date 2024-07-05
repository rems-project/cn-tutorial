// Negative test case: proof should fail 

// The implementation writes to memory location *p, but this location is not
// included in the specification  
void memory_neg_1( int *p )
{
  *p = 1; 
}