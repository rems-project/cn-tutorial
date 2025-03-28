#include "../cn_malloc.h"

struct sllist *malloc__sllist()
/*@ ensures take R = W<struct sllist>(return); @*/
{
  return cn_malloc(sizeof(struct sllist));
}

void free__sllist (struct sllist *p)
/*@ requires take P = W<struct sllist>(p); @*/
{
  cn_free_sized(p, sizeof(struct sllist));
}
