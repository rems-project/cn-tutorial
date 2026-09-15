#include "free.h"
#include "ref.h"
#include "slf0_basic_incr.c"

unsigned int succ_using_incr (unsigned int n)
/*@ requires n < MAXu32();
    ensures return == n + 1; @*/
{
  unsigned int *p = refUnsignedInt(n);
  incr(p);
  unsigned int x = *p;
  free__unsigned_int(p);
  return x;
}
