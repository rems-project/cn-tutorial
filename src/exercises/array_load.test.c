unsigned int readi (unsigned int *p, unsigned int n, unsigned int i)
/*@ requires take A = each(u32 j; j < n)
                      { RW<unsigned int>(array_shift<unsigned int>(p,j)) };
             i < n; 
    ensures take A_post = each(u32 j; j < n) 
                          { RW<unsigned int>(array_shift<unsigned int>(p,j)) };
            return == A[i];
@*/
{
  return p[i];
}
