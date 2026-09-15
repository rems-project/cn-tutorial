#include "slf0_basic_incr.c"


void incr_two (unsigned int *p, unsigned int *q)
/*@ requires take n1 = RW(p);
             n1 + 2 <= MAXu32();
             ptr_eq(q,p);
    ensures take n2 = RW(p);
            n2 == n1 + 2;
@*/
{
  incr(p);
  incr(q);
}



void aliased_call (unsigned int *p)
/*@ requires take n1 = RW(p);
             n1 + 2 <= MAXu32();
    ensures  take n2 = RW(p);
             n2 == n1 + 2;
@*/
{
  incr_two(p, p);
}
