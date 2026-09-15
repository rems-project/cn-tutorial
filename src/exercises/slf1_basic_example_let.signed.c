int doubled (int n)
/* --BEGIN-- */
/*@ requires MINi32() <= n - 1; n + 1 <= MAXi32();
             MINi32() <= n + n; n + n <= MAXi32();
    ensures return == n * 2;
@*/
/* --END-- */
{
  int a = n+1;
  int b = n-1;
  return a+b;
}
