void swap_array (int *p, unsigned long n, unsigned long i, unsigned long j)
/* --BEGIN-- */
/*@ requires take a1 = each(u64 k; 0u64 <= k && k < n) { Owned<int>(array_shift<int>(p,k)) };
             0u64 <= i && i < n;
             0u64 <= j && j < n;
             j != i;
    ensures take a2 = each(u64 k; 0u64 <= k && k < n) { Owned<int>(array_shift<int>(p,k)) };
            a2 == a1[i: a1[j], j: a1[i]];
@*/
/* --END-- */
{
/* --BEGIN-- */
  /*@ extract Owned<int>, i; @*/
/* --END-- */
  int tmp = p[i];
/* --BEGIN-- */
  /*@ extract Owned<int>, j; @*/
/* --END-- */
  p[i] = p[j];
  p[j] = tmp;
}
