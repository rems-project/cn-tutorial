unsigned int example_let (unsigned int n) 
/*@ requires MINu32() < n && 2*n <= MAXu32();
    ensures return == 2 * n;
@*/
{
  unsigned int a = n+1;
  unsigned int b = n-1;
  return a+b;
}


