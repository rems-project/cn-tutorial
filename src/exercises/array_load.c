unsigned int read (unsigned int *p, unsigned int n, unsigned int i)
/*@ requires take A = each(integer j; j < n)
                      { RW<unsigned int>(array_shift<unsigned int>(p,j)) };
             i < n; 
    ensures take A_post = each(integer j; j < n) 
                          { RW<unsigned int>(array_shift<unsigned int>(p,j)) };
            return == A[i];
@*/
{
  /*@ focus RW<unsigned int>, i; @*/
  /*@ instantiate i; @*/
  return p[i];
}
