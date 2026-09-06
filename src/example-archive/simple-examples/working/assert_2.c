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
  assert(*x == 0 && *y == 7);
  *y = 0;
  assert(*x == 0 && *y == 0);
}
