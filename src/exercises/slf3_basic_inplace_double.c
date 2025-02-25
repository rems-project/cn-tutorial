void inplace_double (int *p)
/* --BEGIN-- */
/*@ requires take P = Owned<int>(p);
             let M = 2i64 * ((i64) P);
             (i64) MINi32() <= M; M <= (i64) MAXi32();
    ensures  take P_post = Owned<int>(p);
             P_post == (i32) M;
@*/
/* --END-- */
{
  int n = *p;
  int m = n + n;
  *p = m;
}
