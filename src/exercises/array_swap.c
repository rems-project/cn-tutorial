void array_swap (int *p, int n, int i, int j)
/* --BEGIN-- */
/*@ requires take a1 = each(integer k; 0 <= k && k < n) { RW<int>(array_shift<int>(p,k)) };
             0 <= i && i < n;
             0 <= j && j < n;
             j != i;
    ensures take a2 = each(integer k; 0 <= k && k < n) { RW<int>(array_shift<int>(p,k)) };
            a2 == a1[i: a1[j], j: a1[i]];
@*/
/* --END-- */
{
/* --BEGIN-- */
  /*@ focus RW<int>, i; @*/
  /*@ instantiate i; @*/
/* --END-- */
  int tmp = p[i];
/* --BEGIN-- */
  /*@ focus RW<int>, j; @*/
  /*@ instantiate j; @*/
/* --END-- */
  p[i] = p[j];
  p[j] = tmp;
}
