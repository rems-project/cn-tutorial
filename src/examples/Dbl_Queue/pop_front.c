#include "./headers.h"

int pop_front (struct dbl_queue* q)
/*@ requires (!is_null(q));
             take Before = Dbl_Queue_Fwd_At(q);
             Before != Seq_Nil{};
    ensures  take After = Dbl_Queue_Fwd_At(q);
             After == tl(Before);
             hd(Before) == return;
@*/
{
    /*@ split_case(is_null(q->front)); @*/

    if (q->front == q->back) { // singleton list case
        int data = q->front->data;
        free_node(q->front);
        q->front = 0;
        q->back = 0;
        return data;

    } else {
        /*@ split_case(ptr_eq(q->front->next, q->back)); @*/

        struct node *front = q->front;
        int data = front->data;
        front->next->prev = 0;
        q->front = front->next;
        free_node(front);

        /*@ split_case(ptr_eq(q->front->next, q->back)); @*/
        return data;
    }
}