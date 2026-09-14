// Assert and prove a property about memory cells 

void assert_2(int *x, int *y)
/*@ requires 
      take Xpre = RW<int>(x); 
      take Ypre = RW<int>(y);
      *x == 7; *y == 7;
    ensures 
      take Xpost = RW<int>(x);
      take Ypost = RW<int>(y);
      *x == 0; *y == 0; @*/
{
  *x = 0;
  #ifdef CN_INSTRUMENT
  /*@ assert(*x == 0 && *y == 7); @*/
  #else
  assert(*x == 0 && *y == 7);
  #endif
  *y = 0;
  #ifdef CN_INSTRUMENT
  /*@ assert(*x == 0 && *y == 0); @*/
  #else
  assert(*x == 0 && *y == 0);
  #endif
}

int main(void)
/*@ trusted; @*/
{
  int x = 7;
  int y = 7;
  assert_2(&x, &y);
}