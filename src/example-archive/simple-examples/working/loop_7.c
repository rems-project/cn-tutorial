// A loop where the number of iterations depends on an input value. Note that
// the `{n}unchanged` clause is very important here. Otherwise, CN concludes
// that the value of `n` is unknown, which causes the proof to fail 

int loop_7(int n)
/*@ requires 0i32 < n @*/
/*@ ensures return == n @*/
{
  int i = 0;
  while (i < n)
  /*@ inv 0i32 <= i; 
          i <= n;
          {n}unchanged @*/ 
  {
    i = i + 1;
  };
  return i;
}
