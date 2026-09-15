unsigned int quadruple (unsigned int n)
/*@ requires 4 * n <= MAXu32();
    ensures return == 4 * n; @*/
{
  unsigned int m = n + n;
  return m + m;
}
