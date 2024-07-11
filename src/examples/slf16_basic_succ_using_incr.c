// TODO - REVISIT

#include <limits.h>

// #include "free.h"

void freeInt (int *p)
/*@ requires take v = Block<int>(p);
    ensures true;
@*/
{
}

void freeUnsignedInt (unsigned int *p)
/*@ requires take v = Block<unsigned int>(p);
    ensures true;
@*/
{
}

// #include "ref.h"

unsigned int *refUnsignedInt (unsigned int v)
/*@ requires true;
    ensures take vr = Owned(return);
            vr == v;
@*/
{
    return 0;
}


int *refInt (int v)
/*@ requires true;
    ensures take vr = Owned(return);
            vr == v;
@*/
{
    return 0;
}

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

unsigned int succ_using_incr (unsigned int n)
/*@ ensures return == n + 1u32; @*/
{
  unsigned int *p = refUnsignedInt(n);
  incr(p);
  unsigned int x = *p;
  freeUnsignedInt(p);
  return x;
}

int main()
/*@ trusted; @*/
{
    unsigned int n = UINT_MAX;
    unsigned int res = succ_using_incr(n);
    /*@ assert (res == 0u32); @*/
}
