#include "slf4_basic_incr_two.c"

void aliased_call (unsigned int *p)
/*@ requires take n1 = Owned(p)
    ensures take n2 = Owned(p);
            n2 == n1 + 2u32 @*/
{
  incr_two(p, p);
}
