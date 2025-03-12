#include "slf0_basic_incr.c"

void incr_two (unsigned int *p, unsigned int *q)
/*@ requires take n1 = RW(p);
             take m1 = RW(q);
    ensures take n2 = RW(p);
            take m2 = RW(q);
            n2 == n1 + 1u32;
            m2 == m1 + 1u32;
@*/
{
  incr(p);
  incr(q);
}

