unsigned int writei (unsigned int *p, unsigned int n, unsigned int i, unsigned int v)
/*@ requires take A = each(u32 j; j < n)
                      { RW<unsigned int>(array_shift<unsigned int>(p,j)) };
             i < n; 
    ensures take A_post = each(u32 j; j < n) 
                          { RW<unsigned int>(array_shift<unsigned int>(p,j)) }; 
            A_post[i] == v;
@*/
{
  p[i] = v;
}
