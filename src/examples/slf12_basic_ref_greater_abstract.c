#include "slf10_basic_ref.c"

unsigned int *ref_greater (unsigned int *p)
--BEGIN--
/*@ requires take n1 = Owned(p);
             n1 < n1 + 1u32
    ensures  take n2 = Owned(p);
             take m2 = Owned(return);
             n2 == n1;
             m2 > n1
@*/
--END--
{
  unsigned int n = *p;
  unsigned int m = n+1;
  return refUnsignedInt(m);
}
