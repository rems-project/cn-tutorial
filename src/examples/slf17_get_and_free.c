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


unsigned int get_and_free (unsigned int *p)
/*@ requires take v1_ = Owned(p);
    ensures return == v1_; @*/
{
  unsigned int v = *p;
  freeUnsignedInt (p);
  return v;
}

int main() 
/*@ trusted; @*/
{
    unsigned int x = 5;
    unsigned int res = get_and_free(&x); // obviously wrong
    /*@ assert (x == 5u32); @*/
}
