#include "free.h"

unsigned int get_and_free (unsigned int *p)
/*@ requires take P = Owned(p);
    ensures return == P; 
@*/
{
  unsigned int v = *p;
  freeUnsignedInt (p);
  return v;
}
