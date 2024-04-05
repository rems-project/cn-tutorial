void init_array2 (char *p, unsigned int n) 
/*@ requires take a1 = each(u32 i; i < n) { Block<char>( array_shift<char>(p, i)) }
    ensures  take a2 = each(u32 i; i < n) { Owned<char>( array_shift<char>(p, i)) } 
@*/
{
  unsigned int j = 0;
  while (j < n)
--BEGIN--
  /*@ inv j <= n;
          {p} unchanged; {n} unchanged;
          take al = each(u32 i; i < j) { Owned<char>( array_shift<char>(p, i)) };
          take ar = each(u32 i; j <= i && i < n) { Block<char>( array_shift<char>(p, i)) }
  @*/
--END--
  {
    /*@ extract Block<char>, j; @*/
    /*@ extract Owned<char>, j; @*/
    p[j] = 0;
    j++;
  }
}
