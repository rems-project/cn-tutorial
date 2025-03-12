#include "malloc.h"

unsigned int *ref_greater_abstract (unsigned int *p)
/* --BEGIN-- */
/*@ requires take P = RW<unsigned int>(p);
             P < 4294967295u32;
    ensures take P_post = RW<unsigned int>(p);
            take R = RW<unsigned int>(return);
            P == P_post;
            P <= R;
@*/
/* --END-- */
{
  unsigned int* q = mallocUnsignedInt();
  *q = *p + 1;
  return q;
}
