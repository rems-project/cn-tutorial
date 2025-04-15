#include "cn_malloc.h"

unsigned int *malloc_and_set (unsigned int x)
/*@ ensures take P = RW(return);
            P == x;
@*/
{
  unsigned int *p = cn_malloc(sizeof(unsigned int));
  *p = x;
  return p;
}

unsigned int get_and_free (unsigned int *p)
/*@ requires take P = RW(p);
    ensures return == P;
@*/
{
  unsigned int v = *p;
  cn_free_sized(p, sizeof(unsigned int));
  return v;
}

unsigned int tester()
/*@ requires true;
    ensures return == 42u32;
@*/
{
  unsigned int *p = malloc_and_set(42);
  unsigned int v = get_and_free(p);
  return v;
}
