#include "queue_headers.h"

struct queue* IntQueue_empty ()
/* --BEGIN-- */
/*@ ensures take ret = IntQueuePtr(return);
            ret == Nil{};
@*/
/* --END-- */
{
  struct queue *p = mallocIntQueue();
  p->front = 0;
  p->back = 0;
  return p;
}
