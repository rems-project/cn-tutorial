#include <limits.h>
int add(int x, int y)
/* --BEGIN-- */
/*@ requires let sum = (i64) x + (i64) y;
             (i64)MINi32() <= sum; sum <= (i64)MAXi32();
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
