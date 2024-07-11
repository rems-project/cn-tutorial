// TODO - REVISIT

#include <limits.h>

// #include "slf0_basic_incr.c"

void incr (unsigned int *p)
/* --BEGIN-- */
/*@ requires take n1 = Owned<unsigned int>(p);
    ensures take n2 = Owned<unsigned int>(p);
            n2 == n1 + 1u32;
@*/
/* --END-- */
{
  unsigned int n = *p;
  unsigned int m = n+1;
  *p = m;
}

// #include "slf10_basic_ref.c"

unsigned int *refUnsignedInt (unsigned int v)
/*@ ensures take vr = Owned(return);
            vr == v;
@*/
{
    return 0;
}


unsigned int succ_using_incr_attempt(unsigned int n)
/* --BEGIN-- */
/*@ ensures return == n+1u32; 
@*/
/* --END-- */
{
  unsigned int *p = refUnsignedInt(n);
  incr(p);
  return *p;
}

int main()
/*@ trusted; @*/
{
    unsigned int x = INT_MAX;
    unsigned int res = succ_using_incr_attempt(x);
    /*@ assert (res == 0u32); @*/
}
