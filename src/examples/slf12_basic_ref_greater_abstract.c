// TODO - REVISIT

#include <limits.h>

// #include "slf10_basic_ref.c"

unsigned int *refUnsignedInt (unsigned int v)
/*@ ensures take vr = Owned(return);
            vr == v;
@*/
{
    return 0;
}

unsigned int *ref_greater (unsigned int *p)
/* --BEGIN-- */
/*@ requires take n1 = Owned(p);
             n1 < n1 + 1u32;
    ensures  take n2 = Owned(p);
             take m2 = Owned(return);
             n2 == n1;
             m2 > n1;
@*/
/* --END-- */
{
  unsigned int n = *p;
  unsigned int m = n+1;
  return refUnsignedInt(m);
}

int main()
{
    unsigned int x = UINT_MAX-1;
    unsigned int *p = ref_greater(&x);
    /*@ assert (!ptr_eq(p, &x)); @*/
    /*@ assert (*p == MAXu32());  @*/
}
