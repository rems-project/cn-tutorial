void init_array (char *p, unsigned int n)
/*@ requires take A = each(u32 i; i < n) { 
                         RW<char>( array_shift<char>(p, i)) };
    ensures  take A_post = each(u32 i; i < n) { 
                             RW<char>( array_shift<char>(p, i)) };
@*/
{
  unsigned int j = 0;
  while (j < n)
/* --BEGIN-- */
  /*@ inv take Ai = each(u32 i; i < n) { 
                      RW<char>( array_shift<char>(p, i)) };
          {p} unchanged; 
          {n} unchanged;
  @*/
/* --END-- */
  {
/* --BEGIN-- */
    /*@ focus RW<char>, j; @*/
/* --END-- */
    p[j] = 0;
    j++;
  }
}
