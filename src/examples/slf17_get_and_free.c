#ifndef CN_UTILS
void *cn_malloc(unsigned long);
void cn_free_sized(void*, unsigned long);
#endif

#include <limits.h>

// #include "free.h"

void freeUnsignedInt (unsigned int *p)
/*@ requires take v = Block<unsigned int>(p);
    ensures true;
@*/
{
    cn_free_sized(p, sizeof(unsigned int));
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
    unsigned int *x = cn_malloc(sizeof(int));
    *x = 5;
    unsigned int res = get_and_free(x);
    /*@ assert (res == 5u32); @*/
}
