#ifndef CN_UTILS
#include <stdlib.h>
void *cn_malloc(unsigned long size) {
    return malloc(size);
}
void cn_free_sized(void* p, unsigned long s) {
    free(p);
}
#endif

unsigned int leaky_get (unsigned int *p)
/*@ trusted;
requires
    take v1_ = Owned(p);
ensures
    return == v1_;
@*/
{
  return *p;
}

int main()
/*@ trusted; @*/
{
    unsigned int *x = cn_malloc(sizeof(unsigned int));
    *x = 5;
    unsigned int res = leaky_get(x);
}
