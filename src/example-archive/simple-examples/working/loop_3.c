// A loop where an invariant is necessary to ensure that the variable `acc`
// never overflows.

// TODO: write down a post-condition 

int loop_3(int i)
/*@ requires 
      let MAXi32 = 2147483647; // TODO: lift to library 
      i + 1 <  MAXi32; 
      0 < i; @*/
// TODO: ensures? 
{
  int n = 0;
  int acc = 0;

  while (n != i)
  /*@ inv n <= i; 
          0 <= acc; 
          acc <= n; @*/
  {
    acc = n - acc;
    n++;
  };
  return acc;
}
