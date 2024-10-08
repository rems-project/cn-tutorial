unsigned int array_read_two (unsigned int *p, unsigned long n, unsigned long i, unsigned long j)
/* --BEGIN-- */
/*@ requires take a1 = each(u64 k; 0u64 <= k && k < n) { Owned<unsigned int>(array_shift<unsigned int>(p,k)) };
             0u64 <= i && i < n;
             0u64 <= j && j < n;
             j != i;
    ensures take a2 = each(u64 k; 0u64 <= k && k < n) { Owned<unsigned int>(array_shift<unsigned int>(p,k)) };
            a1 == a2;
            return == a1[i] + a1[j];
@*/
/* --END-- */
{
/* --BEGIN-- */
  /*@ extract Owned<unsigned int>, i; @*/
/* --END-- */
  unsigned int tmp1 = p[i];
/* --BEGIN-- */
  /*@ extract Owned<unsigned int>, j; @*/
/* --END-- */
  unsigned int tmp2 = p[j];
  return (tmp1 + tmp2);
}
