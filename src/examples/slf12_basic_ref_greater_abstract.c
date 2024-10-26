// #include <limits.h>
// Generating C files from CN-annotated source... cn: internal error, uncaught exception:
//     End_of_file

#ifndef CN_UTILS
#include <stdlib.h>
void *cn_malloc(unsigned long size);
void cn_free_sized(void* p, unsigned long s);
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

unsigned int *ref_greater (unsigned int *p)
/* --BEGIN-- */
/*@ requires take n1 = Owned(p);
             n1 < n1 + 1u32;
    ensures  take n2 = Owned(p);
             take m2 = Owned(return);
             n2 == n1;
             m2 > n1;
@*/
/* --END-- */
{
  unsigned int n = *p;
  unsigned int m = n+1;
  return refUnsignedInt(m);
}

int main()
{
    unsigned int x = 100;
    unsigned int *p = ref_greater(&x);
    /*@ assert (!ptr_eq(p, &x)); @*/
    /*@ assert (*p == 101u32);  @*/
}
