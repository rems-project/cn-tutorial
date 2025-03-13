#include "../cn_malloc.h"

struct queue *malloc__queue()
/*@ ensures take R = W<struct queue>(return); @*/
{
  return cn_malloc(sizeof(struct queue));
}

void free__queue (struct queue *p)
/*@ requires take P = W<struct queue>(p); @*/
{
  cn_free_sized(p, sizeof(struct queue));
}

struct queue_cell *malloc__queue_cell()
/*@ ensures take R = W<struct queue_cell>(return); @*/
{
  return cn_malloc(sizeof(struct queue_cell));
}

void free__queue_cell (struct queue_cell *p)
/*@ requires take P = W<struct queue_cell>(p); @*/
{
  cn_free_sized(p, sizeof(struct queue_cell));
}
