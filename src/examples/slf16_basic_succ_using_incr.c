#include "free.h"
#include "ref.h"
#include "slf0_basic_incr.c"

unsigned int succ_using_incr (unsigned int n)
/*@ ensures return == n + 1u32 @*/
{
  unsigned int *p = ref(n);
  incr(p);
  unsigned int x = *p;
  freeUnsignedInt(p);
  return x;
}
