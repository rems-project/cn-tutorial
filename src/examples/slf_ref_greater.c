#include "malloc.h"

unsigned int *ref_greater_abstract (unsigned int *p)
-- BEGIN --
/*@ requires take m1 = Owned<unsigned int>(p);
             m1 < 4294967295u32
    ensures take m2 = Owned<unsigned int>(p);
            take n2 = Owned<unsigned int>(return);
            m1 == m2;
            m1 <= n2
@*/
-- END --
{
  unsigned int* q = mallocUnsignedInt();
  *q = *p + 1;
  return q;
}
