

int
f (int *x)
/*@ requires take xv = RW(x);
             0i32 <= xv && xv < 500i32;
    ensures take xv2 = RW(x); @*/
{
  return ((*x) + (*x));
}
