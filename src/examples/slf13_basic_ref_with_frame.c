#include "slf10_basic_ref.c"

unsigned int *triple_ref_with_frame(unsigned int *p_, unsigned int v)
--BEGIN--
/*@ requires take v_1 = Owned(p_)
    ensures  take v_2 = Owned(p_);
             v_2 == v_1;
             take vr = Owned(return);
             vr == v
@*/
--END--
{
  return ref(v);
}
