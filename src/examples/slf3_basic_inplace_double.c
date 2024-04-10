void inplace_double (int *p)
/* --BEGIN-- */
/*@ requires take n_ = Owned<int>(p);
             let r = 2i64 * ((i64) n_);
             -2147483648i64 <= r; r <= 2147483647i64
    ensures  take m_ = Owned<int>(p);
             m_ == (i32) r
@*/
/* --END-- */
{
  int n = *p;
  int m = n + n;
  *p = m;
}
