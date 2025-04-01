void array_init_rev (char *p, unsigned int n)
/*@ requires take A = each(u32 i; i < n) { 
                        W<char>( array_shift<char>(p, i)) };
    n > 0u32;
    ensures  take A_post = each(u32 i; i < n) { 
                             RW<char>( array_shift<char>(p, i)) };
@*/
{
  unsigned int j = 0;
  while (j < n)
/* --BEGIN-- */
  /*@ inv take Al = each(u32 i; i < n-j) { 
                      W<char>( array_shift<char>(p, i)) };
          take Ar = each(u32 i; n-j <= i && i < n) { 
                      RW<char>( array_shift<char>(p, i)) };
          {p} unchanged; {n} unchanged;
          0u32 <= j && j <= n;
  @*/
/* --END-- */
  {
/* --BEGIN-- */
    /*@ focus W<char>, n-(j+1u32); @*/
    /*@ focus RW<char>, n-(j+1u32); @*/
/* --END-- */
    p[n-(j+1)] = 0;
    j++;
  }
}
