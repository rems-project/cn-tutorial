#ifndef CN_UTILS
#include <stdlib.h>
void *cn_malloc(unsigned long size);
void cn_free_sized(void* p, unsigned long s);
#endif

int *malloc_int()
/*@ trusted;
    ensures take X = Block<int>(return); @*/
{
    return cn_malloc(sizeof(int));
}

void bad_free(int *p)
/*@ trusted; @*/
{
    cn_free_sized(p, sizeof(int));
}

int main()
/*@ trusted; @*/
{
    int *p = malloc_int();
    bad_free(p);
}
