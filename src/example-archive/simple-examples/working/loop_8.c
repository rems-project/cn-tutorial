// A loop with an interesting arithmetic bound  

int loop_8()
/*@ ensures return > 0i32; @*/
{
  int j=0;
  for (int i=0; i<10; i++)
  /*@ inv 0i32 <= j; j <= i * 10i32;
          0i32 <= i; i <= 10i32;
          (i - 1i32) <= j; @*/
  {
    j+=i;
  }
  return j;
} 
