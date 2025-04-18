// This example should be provable because RW locations should be 
// disjoint. But CN currently doesn't enforce this property. 
// See: https://github.com/rems-project/cerberus/issues/295 

void ownership_1(int *a, int *b)
/*@ 
requires 
  take P1 = RW(a); 
  take P2 = RW(b);
ensures 
  a != b; 
@*/
{
  /*@ split_case a == b; @*/
  ; 
}