#include <limits.h>

int abs (int x)
/* --BEGIN-- */
/*@ requires MINi32() < x;
    ensures return == ((x >= 0i32) ? x : (0i32-x));
@*/
/* --END-- */
{
  if (x >= 0) {
    return x;
  }
  else {
    return -x;
  }
}

int main()
/*@ trusted; @*/
{
    int x = abs(INT_MAX);
    /*@ assert (x == MAXi32()); @*/

    int y = abs(INT_MIN+1);
    /*@ assert (y == MAXi32()); @*/

    int z = abs(0);
    /*@ assert (z == 0i32); @*/
}
