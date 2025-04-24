void array_add3 (unsigned int *p, unsigned int n)
/* --BEGIN-- */
/*@ requires take A = each(u32 i; i < n)
                      { RW<unsigned int>(array_shift<unsigned int>(p,i)) };
    ensures take A_post = each(u32 i; i < n)
                          { RW<unsigned int>(array_shift<unsigned int>(p,i)) };
            each (u32 i; i < n)
            { A_post[i] == A[i] + 3u32 };

@*/
/* --END-- */
{
  int i;
  for (i = 0; i < n; i++) {
    p[i] = p[i] + 3;
  }
}