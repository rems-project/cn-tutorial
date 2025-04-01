void array_sort (unsigned int *p, unsigned int n)
/* --BEGIN-- */
/*@ requires take A = each(u32 i; i < n)
                      { RW<unsigned int>(array_shift<unsigned int>(p,i)) };
    ensures take A_post = each(u32 i; i < n)
                          { RW<unsigned int>(array_shift<unsigned int>(p,i)) };
            each (u32 i; i + 1u32 < n && i < n)
            { A_post[i] <= A_post[i + 1u32] };
@*/
/* --END-- */
{
  int i, j;
  for (i = 0; i < n; i++) {
    for (j = 0; j < n; j++) {      
      if (p[i] < p[j]) {
        unsigned int temp = p[i];
        p[i] = p[j];
        p[j] = temp;
      }
    }
  }
}