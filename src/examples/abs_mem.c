#include <limits.h>

int abs_mem (int *p)
/* --BEGIN-- */
/*@ requires take x = Owned<int>(p);
             MINi32() < x;
    ensures take x2 = Owned<int>(p);
            x == x2;
            return == ((x >= 0i32) ? x : (0i32-x));
@*/
/* --END-- */
{
  int x = *p;
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
    int i = INT_MAX;
    int x = abs_mem(&i);
    /*@ assert (x == MAXi32()); @*/

    i = INT_MIN+1;
    int y = abs_mem(&i);
    /*@ assert (y == MAXi32()); @*/

    i = 0;
    int z = abs_mem(&i);
    /*@ assert (z == 0i32); @*/

    // int bad = abs_mem(0);
}
