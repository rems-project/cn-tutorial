void incr (int *p)
/* --BEGIN-- */
/*@ requires take v1 = W<int>(p);
    ensures take v2 = RW<int>(p);
            v2 == v1+1i32; @*/
/* --END-- */
{
  int n = *p;
  int m = n+1;
  *p = m;
}
