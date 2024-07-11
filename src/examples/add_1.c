#include <limits.h>
int add(int x, int y)
/* --BEGIN-- */
/*@ requires let sum = (i64) x + (i64) y;
             -2147483648i64 <= sum; sum <= 2147483647i64;
    ensures return == (i32) sum;
@*/
/* --END-- */
{
  return x+y;
}

int main()
/*@ trusted; @*/
{
    int x = add(INT_MAX-1, 1);
    /*@ assert (x == MAXi32()); @*/

    int y = add(INT_MIN+1, -1);
    /*@ assert (y == MINi32()); @*/
}
