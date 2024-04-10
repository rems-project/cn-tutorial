int quadruple_mem (int *p)
/* --BEGIN-- */
/*@ requires take n = Owned<int>(p);
             let n_ = (i64) n;
             -2147483648i64 <= n_ * 4i64; n_ * 4i64 <= 2147483647i64
    ensures take n2 = Owned<int>(p);
            n2 == n;
            return == 4i32 * n @*/
/* --END-- */
{
  int m = *p + *p;
  return m + m;
}
