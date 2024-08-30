#include "queue_headers.h"

struct queue* Queue_empty ()
/* --BEGIN-- */
/*@ ensures take ret = QueuePtr(return);
            ret == Nil{};
@*/
/* --END-- */
{
  struct queue *p = malloc_queue();
  p->front = 0;
  p->back = 0;
  return p;
}
