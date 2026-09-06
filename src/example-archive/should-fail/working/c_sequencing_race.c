

int
f (int *x)
/*@ requires take xv = RW(x);
             0 <= xv && xv < 500;
    ensures take xv2 = RW(x); @*/
{
  return ((*x) + (*x));
}
