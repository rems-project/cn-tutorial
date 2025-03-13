#include "slf10_basic_ref.c"

unsigned int *triple_ref_with_frame(unsigned int *p_, unsigned int v)
/* --BEGIN-- */
/*@ requires take v_1 = RW(p_);
    ensures  take v_2 = RW(p_);
             v_2 == v_1;
             take vr = RW(return);
             vr == v;
@*/
/* --END-- */
{
  return refUnsignedInt(v);
}
