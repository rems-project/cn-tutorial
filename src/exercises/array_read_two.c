unsigned int array_read_two (unsigned int *p, int n, int i, int j)
/* --BEGIN-- */
/*@ requires take A = each(integer k; 0 <= k && k < n) { 
                        RW<unsigned int>(array_shift<unsigned int>(p,k)) };
             0 <= i && i < n;
             0 <= j && j < n;
             j != i;
	     A[i] + A[j] <= MAXu32();
    ensures take A_post = each(integer k; 0 <= k && k < n) { 
                            RW<unsigned int>(array_shift<unsigned int>(p,k)) };
            A == A_post;
            return == A[i] + A[j];
@*/
/* --END-- */
{
/* --BEGIN-- */
  /*@ focus RW<unsigned int>, i; @*/
  /*@ instantiate i; @*/
/* --END-- */
  unsigned int tmp1 = p[i];
/* --BEGIN-- */
  /*@ focus RW<unsigned int>, j; @*/
  /*@ instantiate j; @*/
/* --END-- */
  unsigned int tmp2 = p[j];
  return (tmp1 + tmp2);
}
