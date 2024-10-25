#ifndef CN_UTILS
#include <stdlib.h>
void *cn_malloc(unsigned long size) {
    return malloc(size);
}
void cn_free_sized(void* p, unsigned long s) {
    free(p);
}
#endif

unsigned int *mallocUnsignedInt()
/*@ trusted;
    ensures take v = Block<unsigned int>(return); !is_null(return); @*/
{
    return cn_malloc(sizeof(unsigned int));
}

unsigned int *refUnsignedInt (unsigned int v)
/*@ ensures take vr = Owned(return);
            vr == v;
@*/
{
    unsigned int *res = mallocUnsignedInt();
    *res = v;
    return res;
}

int main()
/*@ trusted; @*/
{
    unsigned int v = 5;
    unsigned int *p = refUnsignedInt(v);
    /*@ assert (*p == 5u32); @*/
}
