#ifndef CN_UTILS
#include <stdlib.h>
void *cn_malloc(unsigned long size);
void cn_free_sized(void* p, unsigned long s);
#endif

unsigned int deref(unsigned int *p)
/*@ trusted;
requires
    take v1_ = Owned(p);
ensures
    take v2 = Owned(p);
    v1_ == v2;
    return == v1_;
@*/
{
  return *p;
}

int main()
/*@ trusted; @*/
{
    unsigned int *p = cn_malloc(sizeof(unsigned int));
    *p = 5;
    unsigned int x = deref(p);
    /*@ assert (x == 5u32); @*/
    /*@ assert (*p == 5u32); @*/
    cn_free_sized(p, sizeof(unsigned int));
    // double free
    cn_free_sized(p, sizeof(unsigned int));
}
