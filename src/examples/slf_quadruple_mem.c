int quadruple_mem (int *p)
/* --BEGIN-- */
/*@ requires take n = Owned<int>(p);
             let N = (i64) n;
             (i64)MINi32() <= N * 4i64; N * 4i64 <= (i64)MAXi32();
    ensures take n2 = Owned<int>(p);
            n2 == n;
            return == 4i32 * n;
 @*/
/* --END-- */
{
  int m = *p + *p;
  return m + m;
}
