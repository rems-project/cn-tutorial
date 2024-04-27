int quadruple (int n)
/* --BEGIN-- */
/*@ requires let n_ = (i64) n;
             -2147483648i64 <= n_ * 4i64; n_ * 4i64 <= 2147483647i64;
    ensures return == 4i32 * n;
 @*/
/* --END-- */
{
  int m = n + n;
  return m + m;
}
