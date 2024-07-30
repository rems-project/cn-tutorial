#include "./headers.h"

struct dbl_queue *empty_dbl_queue()
/* --BEGIN-- */
/*@ ensures 
        !is_null(return);
        take ret = Dbl_Queue_Fwd_At(return);
        ret == Seq_Nil{};
@*/
/* --END-- */
{
  struct dbl_queue *q = malloc_dbl_queue();
  q->front = 0;
  q->back = 0;
  return q;
}