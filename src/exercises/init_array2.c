void init_array2 (char *p, unsigned int n)
/*@ requires take A = each(u32 i; i < n) { 
                        W<char>( array_shift<char>(p, i)) };
    ensures  take A_post = each(u32 i; i < n) { 
                             RW<char>( array_shift<char>(p, i)) };
@*/
{
  unsigned int j = 0;
  while (j < n)
/* --BEGIN-- */
  /*@ inv take Al = each(u32 i; i < j) { 
                      RW<char>( array_shift<char>(p, i)) };
          take Ar = each(u32 i; j <= i && i < n) { 
                      W<char>( array_shift<char>(p, i)) };
          {p} unchanged; {n} unchanged;
          j <= n;
  @*/
/* --END-- */
  {
/* --BEGIN-- */
    /*@ focus W<char>, j; @*/
    /*@ focus RW<char>, j; @*/
/* --END-- */
    p[j] = 0;
    j++;
  }
}
