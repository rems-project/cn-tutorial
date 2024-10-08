int read (int *p, unsigned long n, unsigned long i)
/*@ requires take a1 = each(u64 j; 0u64 <= j && j < n) { Owned<int>(array_shift<int>(p,j)) };
             0u64 <= i && i < n;
    ensures take a2 = each(u64 j; 0u64 <= j && j < n) { Owned<int>(array_shift<int>(p,j)) };
            a1 == a2;
            return == a1[i];
@*/
{
  /*@ extract Owned<int>, i; @*/
  return p[i];
}
