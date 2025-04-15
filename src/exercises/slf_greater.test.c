#include "cn_malloc.h"

unsigned int *incr (unsigned int *p)
/* --BEGIN-- */
/*@ requires take P = RW<unsigned int>(p);
    ensures take P_post = RW<unsigned int>(p);
            take Q = RW<unsigned int>(return);
            P == P_post;
            Q == P + 1u32;
@*/
/* --END-- */
{
  unsigned int* q = cn_malloc(sizeof(unsigned int));
  *q = *p + 1;
  return q;
}
