// A loop with an interesting arithmetic bound  

int loop_8()
/*@ ensures return > 0; @*/
{
  int j=0;
  for (int i=0; i<10; i++)
  /*@ inv 0 <= j; j <= i * 10;
          0 <= i; i <= 10;
          (i - 1) <= j; @*/
  {
    j+=i;
  }
  return j;
} 
