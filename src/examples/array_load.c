int read (int *p, unsigned long n, unsigned long i)
/*@ requires take a1 = each(u64 j; 0u64 <= j && j < n) {
                          Owned<int>(array_shift<int>(p,j)) };
             0u64 <= i && i < n;
             n > 0u64;
    ensures take a2 = each(u64 j; 0u64 <= j && j < n) {
                            Owned<int>(array_shift<int>(p,j)) }; @*/
{
  /*@ extract Owned<int>, 0u64; @*/
  return p[0];
}
