// Assert and prove a property about memory cells 

void assert_2(int *x, int *y)
/*@ requires 
      take Xpre = Owned<int>(x); 
      take Ypre = Owned<int>(y);
      *x == 7i32; *y == 7i32 @*/
/*@ ensures 
      take Xpost = Owned<int>(x);
      take Ypost = Owned<int>(y);
      *x == 0i32; *y == 0i32 @*/
{
  *x = 0;
  assert(*x == 0 && *y == 7);
  *y = 0;
  assert(*x == 0 && *y == 0);
}
