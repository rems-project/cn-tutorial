#ifndef CN_UTILS
#include <stdlib.h>
void *cn_malloc(unsigned long size) {
    return malloc(size);
}
void cn_free_sized(void* p, unsigned long s) {
    free(p);
}
#endif

unsigned int *mkref(unsigned int x)
/*@ trusted;
requires
    true;
ensures
    take v1_ = Owned(return);
    v1_ == x;
@*/
{
  unsigned int *p = cn_malloc(sizeof(unsigned int));
  *p = x;
  return p;
}

int main()
/*@ trusted; @*/
{
    unsigned int *p = mkref(5);
    /*@ assert (*p == 5u32); @*/
    cn_free_sized(p, sizeof(unsigned int));
}
