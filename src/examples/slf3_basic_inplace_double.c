void inplace_double (int *p)
/* --BEGIN-- */
/*@ requires take N = Owned<int>(p);
             let r = 2i64 * ((i64) N);
             (i64)MINi32() <= r; r <= (i64)MAXi32();
    ensures  take m_ = Owned<int>(p);
             m_ == (i32) r;
@*/
/* --END-- */
{
  int n = *p;
  int m = n + n;
  *p = m;
}
