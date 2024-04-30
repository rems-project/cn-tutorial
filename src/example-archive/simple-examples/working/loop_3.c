// A loop where an invariant is necessary to ensure that the variable `acc`
// never overflows.

// TODO: write down a post-condition 

int loop_3(int i)
/*@ requires 
      let MAXi32 = (i64) 2147483647i64; // TODO: lift to library 
      (i64) i + 1i64 <  MAXi32; 
      0i32 < i; @*/
// TODO: ensures? 
{
  int n = 0;
  int acc = 0;

  while (n != i)
  /*@ inv n <= i; 
          0i32 <= acc; 
          acc <= n; @*/
  {
    acc = n - acc;
    n++;
  };
  return acc;
}
