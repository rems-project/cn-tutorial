void incr (int *p)
--BEGIN--
/*@ requires take v1 = Block<int>(p);
    ensures take v2 = Owned<int>(p);
            v2 == v1+1i32 @*/
--END--
{
  int n = *p;
  int m = n+1;
  *p = m;
}
