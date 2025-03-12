int read (unsigned int *p, unsigned int n, unsigned int i)
/*@ requires take A = each(u32 j; 0u32 <= j && j < n) { 
                        Owned<unsigned int>(array_shift<int>(p,j)) };
             i < n; 
    ensures take A_post = each(u32 j; 0u32 <= j && j < n) { 
                             Owned<unsigned int>(array_shift<int>(p,j)) }; 
@*/
{
  return p[i];
}
