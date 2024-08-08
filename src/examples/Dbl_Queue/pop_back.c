#include "./headers.h"
int pop_back (struct dbl_queue* q)
/* --BEGIN-- */
/*@ requires (!is_null(q));
             take Before = Dbl_Queue_Bwd_At(q);
             Before != Seq_Nil{};
    ensures  take After = Dbl_Queue_Bwd_At(q);
             After == tl(Before);
             hd(Before) == return;
@*/
/* --END-- */
{
            /* --BEGIN-- */
    /*@ split_case(is_null(q->back)); @*/
    /*@ assert(!is_null(q->front)); @*/
            /* --END-- */
    if (q->front == q->back) { // singleton list case
        int data = q->back->data;
        free_node(q->back);
        q->front = 0;
        q->back = 0;
        return data;

    } else {
                /* --BEGIN-- */
        /*@ split_case(ptr_eq((*(*q).back).prev, (*q).front)); @*/
                /* --END-- */
        struct node *back = q->back;
        int data = back->data;
        back->prev->next = 0;
        q->back = back->prev;
        free_node(back);
                /* --BEGIN-- */
        /*@ split_case(ptr_eq((*(*q).back).prev, (*q).front)); @*/
                /* --END-- */
        return data;
    }
}