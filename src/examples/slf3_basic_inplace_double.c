#include <limits.h>

void inplace_double (int *p)
/* --BEGIN-- */
/*@ requires take n_ = Owned<int>(p);
             let r = 2i64 * ((i64) n_);
             (i64)MINi32() <= r; r <= (i64)MAXi32();
    ensures  take m_ = Owned<int>(p);
             m_ == (i32) r;
@*/
/* --END-- */
{
  int n = *p;
  int m = n + n;
  *p = m;
}

int main()
{
    int x = 50000;
    inplace_double(&x);
    /*@ assert (x == 100000i32); @*/

    // uncomment for failure
    // x = INT_MAX / 2 + 1;
    // inplace_double(&x);
}
