#include "malloc.h"

unsigned int *ref_greater (unsigned int *p)
/*@ requires take m1 = Owned<unsigned int>(p)
    ensures take m2 = Owned<unsigned int>(p);
            take n2 = Owned<unsigned int>(return);
            m1 == m2;
            m1 <= n2

@*/
{
  unsigned int* q = mallocUnsignedInt();
  *q = *p;
  return q;
}
