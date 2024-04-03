#include "free.h"

void loop_free (int *p, int n)
/*@ requires n > 0i32;
             take a1 = each(i32 j; 0i32 <= j && j < n) { Owned<int>(array_shift<int>(p, j)) }
@*/
{
  int i = 0;
  while (i < n)
--BEGIN--
  /*@ inv {n} unchanged;
          {p} unchanged;
          0i32 <= i && i <= n;
          take ai = each(i32 j; i <= j && j < n) { Owned<int>(array_shift<int>(p, j)) }
  @*/
--END--
  {
--BEGIN--
    /*@ extract Owned<int>, i; @*/
--END--
    free_(p+i);
    i++;
  }
}
