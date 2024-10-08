#include "./headers.h"

// Given a dbl queue pointer, inserts a new node
// to the front of the list
void push_front (struct dbl_queue* q, int element)
/*@ requires (!is_null(q));
             take Before = Dbl_Queue_Fwd_At(q);
    ensures  take After = Dbl_Queue_Fwd_At(q);
             After == Seq_Cons{head: element, tail: Before};
@*/
{
    struct node *new_node = malloc_node();
    new_node->data = element;
    new_node->next = q->front;
    new_node->prev = 0;

    if (q->front == 0) {
        // in this case, the queue is empty
        q->back = new_node;
        q->front = new_node;
    } else {
        /*@ split_case(ptr_eq(q->front, q->back)); @*/
        /*@ split_case(ptr_eq(q->front->next, q->back)); @*/
        q->front->prev = new_node;
        q->front = new_node;
    }
}

