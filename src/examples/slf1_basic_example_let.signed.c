#include <limits.h>

int doubled (int n)
/* --BEGIN-- */
/*@ requires let n_ = (i64) n;
             (i64)MINi32() <= n_ - 1i64; n_ + 1i64 <= (i64)MAXi32();
             (i64)MINi32() <= n_ + n_; n_ + n_ <= (i64)MAXi32();
    ensures return == n * 2i32;
@*/
/* --END-- */
{
  int a = n+1;
  int b = n-1;
  return a+b;
}

int main()
{
    int x = 50000;
    int res = doubled(x);
    /*@ assert (res == 2i32 * x); @*/

    // uncomment for fail
    // x = INT_MAX;
    // res = doubled(x);
}
