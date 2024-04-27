unsigned int quadruple (unsigned int n)
/*@ ensures return == 4u32 * n; @*/
{
  unsigned int m = n + n;
  return m + m;
}
