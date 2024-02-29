#include "slf0_basic_incr.c"

void incr_two (unsigned int *p, unsigned int *q)
/*@ requires take n1 = Owned(p);
             take m1 = Owned(q)
    ensures take n2 = Owned(p);
            take m2 = Owned(q);
            n2 == n1 + 1u32;
            m2 == m1 + 1u32    
@*/
{
  incr(p);
  incr(q);
}

