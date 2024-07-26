unsigned int quadruple (unsigned int n)
/*@ ensures return == 4u32 * n; @*/
{
  unsigned int m = n + n;
  return m + m;
}
int main()
{
    unsigned int x = 50000;
    unsigned int res = quadruple(x);
    /*@ assert (res == 200000u32); @*/
    // wrap-around so passes
    x = (0x7fffffff * 2U + 1U) / 4 + 1;
    res = quadruple(x);
    /*@ assert (res == 4u32 * x); @*/
}
