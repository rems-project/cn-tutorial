// TODO - REVISIT

void init_array2 (char *p, unsigned int n)
/*@ requires take a1 = each(u32 i; i < n) { Block<char>( array_shift<char>(p, i)) };
    ensures  take a2 = each(u32 i; i < n) { Owned<char>( array_shift<char>(p, i)) };
@*/
{
  unsigned int j = 0;
  while (j < n)
/* --BEGIN-- */
  /*@ inv take al = each(u32 i; i < j) { Owned<char>( array_shift<char>(p, i)) };
          take ar = each(u32 i; j <= i && i < n) { Block<char>( array_shift<char>(p, i)) };
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

int main()
/*@ trusted; @*/
{
    char a[3] = { 0, 1, 2 };

    init_array2(a, 3);

    char *first = a;
    /*@ assert (*first == 0u8); @*/

    char *second = a + 1;
    /*@ assert (*second == 0u8); @*/

    char *third = a + 2;
    /*@ assert (*third == 0u8); @*/
}
