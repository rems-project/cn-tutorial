void init_array2 (char *p, unsigned long n)
/*@ requires take a1 = each(u64 i; i < n) { Block<char>( array_shift<char>(p, i)) };
    ensures  take a2 = each(u64 i; i < n) { Owned<char>( array_shift<char>(p, i)) };
@*/
{
  unsigned long j = 0;
  while (j < n)
/* --BEGIN-- */
  /*@ inv take al = each(u64 i; i < j) { Owned<char>( array_shift<char>(p, i)) };
          take ar = each(u64 i; j <= i && i < n) { Block<char>( array_shift<char>(p, i)) };
          {p} unchanged; {n} unchanged;
          j <= n;
  @*/
/* --END-- */
  {
/* --BEGIN-- */
    /*@ extract Block<char>, j; @*/
    /*@ extract Owned<char>, j; @*/
/* --END-- */
    p[j] = 0;
    j++;
  }
}
