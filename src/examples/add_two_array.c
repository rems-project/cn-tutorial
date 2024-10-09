unsigned int array_read_two (unsigned int *p, int n, int i, int j)
/* --BEGIN-- */
/*@ requires take A = each(i32 k; 0i32 <= k && k < n) { 
                        Owned<unsigned int>(array_shift<unsigned int>(p,k)) };
             0i32 <= i && i < n;
             0i32 <= j && j < n;
             j != i;
    ensures take A_post = each(i32 k; 0i32 <= k && k < n) { 
                            Owned<unsigned int>(array_shift<unsigned int>(p,k)) };
            A == A_post;
            return == A[i] + A[j];
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
