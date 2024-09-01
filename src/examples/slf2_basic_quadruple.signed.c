int quadruple (int n)
/* --BEGIN-- */
/*@ requires let N = (i64) n;
             (i64)MINi32() <= N * 4i64; N * 4i64 <= (i64)MAXi32();
    ensures return == 4i32 * n;
 @*/
/* --END-- */
{
  int m = n + n;
  return m + m;
}
