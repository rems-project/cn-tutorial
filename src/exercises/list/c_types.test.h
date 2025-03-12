#include "../cn_malloc.h"

struct sllist {
  int head;
  struct sllist* tail;
};

struct sllist *malloc__sllist()
/*@ ensures take R = Block<struct sllist>(return);
@*/
{
  return cn_malloc(sizeof(struct sllist));
}

void free__sllist (struct sllist *p)
/*@ requires take P = Block<struct sllist>(p);
@*/
{
  cn_free_sized(p, sizeof(struct sllist));
}
