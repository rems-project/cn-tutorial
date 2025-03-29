#include "free.h"

unsigned int get_and_free (unsigned int *p)
/*@ requires take P = RW(p);
    ensures return == P; 
@*/
{
  unsigned int v = *p;
  free__unsigned_int (p);
  return v;
}
