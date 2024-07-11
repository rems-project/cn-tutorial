#include <limits.h>

int add(int x, int y)
/* --BEGIN-- */
/*@ requires let sum = (i64) x + (i64) y;
             -2147483648i64 <= sum; sum <= 2147483647i64; @*/
/* --END-- */
{
  return x+y;
}

int main()
/*@ trusted; @*/
{
    add(INT_MAX-1, 1);

    add(INT_MIN+1, -1);
}
