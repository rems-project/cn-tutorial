int read (unsigned *p, unsigned n, unsigned i)
/*@ requires take A = each(u32 j; 0u32 <= j && j < n) { 
                        Owned<unsigned>(array_shift<int>(p,j)) };
             0u32 <= i && i < n; 
    ensures take A_post = each(u32 j; 0u32 <= j && j < n) { 
                        Owned<unsigned>(array_shift<int>(p,j)) }; 
@*/
{
  return p[i];
}
