#include "free.h"

unsigned int get_and_free (unsigned int *p)
/*@ requires take v1_ = Owned(p)
    ensures return == v1_ @*/
{
  unsigned int v = *p;
  free_ (p);
  return v;
}
