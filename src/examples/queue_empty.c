// TODO - REVISIT

#include "queue_headers.h"

struct int_queue* IntQueue_empty ()
/* --BEGIN-- */
/*@ ensures take ret = IntQueuePtr(return);
            ret == Seq_Nil{};
@*/
/* --END-- */
{
  struct int_queue *p = mallocIntQueue();
  p->front = 0;
  p->back = 0;
  return p;
}

int main()
/*@ trusted; @*/
{
}
