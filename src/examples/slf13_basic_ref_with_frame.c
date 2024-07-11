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

unsigned int *triple_ref_with_frame(unsigned int *p_, unsigned int v)
/* --BEGIN-- */
/*@ requires take v_1 = Owned(p_);
    ensures  take v_2 = Owned(p_);
             v_2 == v_1;
             take vr = Owned(return);
             vr == v;
@*/
/* --END-- */
{
  return refUnsignedInt(v);
}

int main()
/*@ trusted; @*/
{
    unsigned int v = 5;
    unsigned int w = 6;
    unsigned int *p = &w;

    unsigned int *q = triple_ref_with_frame(p, v);
    /*@ assert (v == 5u32); @*/
    /*@ assert (w == 6u32); @*/
    /*@ assert (!ptr_eq(q, p)); @*/
    /*@ assert (*q == 6u32); @*/

}
