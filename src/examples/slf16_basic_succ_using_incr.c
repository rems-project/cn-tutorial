// #include <limits.h>
// Generating C files from CN-annotated source... cn: internal error, uncaught exception:
//     End_of_file

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

void freeUnsignedInt (unsigned int *p)
/*@ requires take v = Block<unsigned int>(p);
    ensures true;
@*/
{
    cn_free_sized(p, sizeof(int));
}

// #include "ref.h"

unsigned int *refUnsignedInt (unsigned int v)
/*@ ensures take vr = Owned(return);
            vr == v;
@*/
{
    unsigned int *res = mallocUnsignedInt();
    *res = v;
    return res;
}

// #include "slf0_basic_incr.c"

void incr (unsigned int *p)
/* --BEGIN-- */
/*@ requires take n1 = Owned<unsigned int>(p);
    ensures take n2 = Owned<unsigned int>(p);
            n2 == n1 + 1u32;
@*/
/* --END-- */
{
  unsigned int n = *p;
  unsigned int m = n+1;
  *p = m;
}

unsigned int succ_using_incr (unsigned int n)
/*@ ensures return == n + 1u32; @*/
{
  unsigned int *p = refUnsignedInt(n);
  incr(p);
  unsigned int x = *p;
  freeUnsignedInt(p);
  return x;
}

int main()
/*@ trusted; @*/
{
    unsigned int n = 100;
    unsigned int res = succ_using_incr(n);
    /*@ assert (res == 101u32); @*/
}
