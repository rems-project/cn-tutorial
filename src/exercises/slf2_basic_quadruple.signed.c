int quadruple (int n)
/* --BEGIN-- */
/*@ requires MINi32() <= n * 4; n * 4 <= MAXi32();
    ensures return == 4 * n;
 @*/
/* --END-- */
{
  int m = n + n;
  return m + m;
}
