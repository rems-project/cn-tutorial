#include "../cn_malloc.h"

struct dllist *malloc__dllist()
/*@ ensures take R = W<struct dllist>(return); @*/
{
  return cn_malloc(sizeof(struct dllist));
}

void free__dllist (struct dllist *p)
/*@ requires take P = W<struct dllist>(p); @*/
{
  cn_free_sized(p, sizeof(struct dllist));
}
