#include "./headers.verif.h"

struct queue* empty_queue ()
/* --BEGIN-- */
/*@ ensures take ret = QueuePtr_At(return);
            ret == Nil{};
@*/
/* --END-- */
{
  struct queue *p = malloc_queue();
  p->front = 0;
  p->back = 0;
  return p;
}
