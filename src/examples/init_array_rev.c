void init_array2 (char *p, unsigned int n)
/*@ requires take a1 = each(u32 i; 0u32 <= i && i < n) { Block<char>( array_shift<char>(p, i)) };
    n > 0u32;
    ensures  take a2 = each(u32 i; 0u32 <= i && i < n) { Owned<char>( array_shift<char>(p, i)) };
@*/
{
  unsigned int j;
  j= 0;

  while (j < n)
/* --BEGIN-- */
  /*@ inv take al = each(u32 i; i < n-j) { Block<char>( array_shift<char>(p, i)) };
          take ar = each(u32 i; n-j <= i && i < n) { Owned<char>( array_shift<char>(p, i)) };
          {p} unchanged; {n} unchanged;
          0u32 <= j && j <= n;
  @*/
/* --END-- */
  {
/* --BEGIN-- */
    /*@ extract Block<char>, n-(j+1u32); @*/
    /*@ extract Owned<char>, n-(j+1u32); @*/
/* --END-- */
    p[n-(j+1)] = 0;
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
