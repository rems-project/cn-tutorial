#include "slf0_basic_incr.c"
#include "slf10_basic_ref.c"

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
