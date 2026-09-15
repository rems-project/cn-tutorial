void array_init_rev (char *p, unsigned int n)
/*@ requires take A = each(integer i; i < n) { 
                        RW<char>( array_shift<char>(p, i)) };
    ensures  take A_post = each(integer i; i < n) { 
                             RW<char>( array_shift<char>(p, i)) };
@*/
{
  unsigned int j = 0;
  while (j < n)
/* --BEGIN-- */
  /*@ inv take Al = each(integer i; i < n-j) { 
                      RW<char>( array_shift<char>(p, i)) };
          take Ar = each(integer i; n-j <= i && i < n) { 
                      RW<char>( array_shift<char>(p, i)) };
          {p} unchanged; {n} unchanged;
          j <= n;
  @*/
/* --END-- */
  {
/* --BEGIN-- */
    /*@ focus RW<char>, n-(j+1); @*/
    /*@ instantiate n-(j+1); @*/
/* --END-- */
    p[n-(j+1)] = 0;
    j++;
  }
}
