void swap_array (int *p, int n, int i, int j)
/* --BEGIN-- */
/*@ requires take a1 = each(i32 k; 0i32 <= k && k < n) { RW<int>(array_shift<int>(p,k)) };
             0i32 <= i && i < n;
             0i32 <= j && j < n;
             j != i;
    ensures take a2 = each(i32 k; 0i32 <= k && k < n) { RW<int>(array_shift<int>(p,k)) };
            a2 == a1[i: a1[j], j: a1[i]];
@*/
/* --END-- */
{
/* --BEGIN-- */
  /*@ focus RW<int>, i; @*/
/* --END-- */
  int tmp = p[i];
/* --BEGIN-- */
  /*@ focus RW<int>, j; @*/
/* --END-- */
  p[i] = p[j];
  p[j] = tmp;
}
