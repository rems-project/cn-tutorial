#ifndef CN_UTILS
#include <stdlib.h>
void *cn_malloc(unsigned long size);
void cn_free_sized(void* p, unsigned long s);
#endif

unsigned int read_and_free(unsigned int *p)
/*@ trusted;
requires
    take v1_ = Owned(p);
ensures
    return == v1_;
@*/
{
  unsigned int result = *p;
  cn_free_sized(p, sizeof(unsigned int));
  return result;
}

int main()
/*@ trusted; @*/
{
    unsigned int *x = cn_malloc(sizeof(unsigned int));
    *x = 5;
    unsigned int res = read_and_free(x);
    /*@ assert (res == 5u32); @*/
}
