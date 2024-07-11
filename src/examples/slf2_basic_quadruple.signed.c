#include <limits.h>

int quadruple (int n)
/* --BEGIN-- */
/*@ requires let n_ = (i64) n;
             (i64)MINi32() <= n_ * 4i64; n_ * 4i64 <= (i64)MAXi32();
    ensures return == 4i32 * n;
 @*/
/* --END-- */
{
  int m = n + n;
  return m + m;
}

int main()
{
    int x = 50000;
    int res = quadruple(x);
    /*@ assert (res == 200000i32); @*/

    // uncomment for failure
    // x = INT_MAX / 4 + 1;
    // res = quadruple(x);
}
