#include "./headers.h"

// Given a dbl queue pointer, inserts a new node
// to the back of the list
void push_back (struct dbl_queue* q, int element)
/* --BEGIN-- */
/*@ requires (!is_null(q));
             take Before = Dbl_Queue_Bwd_At(q);
    ensures  take After = Dbl_Queue_Bwd_At(q);
             After == Seq_Cons{head: element, tail: Before};
@*/
/* --END-- */
{
    struct node *new_node = malloc_node();
    new_node->data = element;
    new_node->next = 0;
    new_node->prev = q->back;
            /* --BEGIN-- */
    /*@ split_case(ptr_eq((*q).front, (*q).back)); @*/
            /* --END-- */
    if (q->back != 0) {
                /* --BEGIN-- */
        /*@ split_case(ptr_eq((*(*q).back).prev, (*q).front)); @*/
                /* --END-- */
        q->back->next = new_node;
        q->back = new_node;
        return;

    } else {
        // in this case, the queue is empty
        q->back = new_node;
        q->front = new_node;
        return;
    }
}