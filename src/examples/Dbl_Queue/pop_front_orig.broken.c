#include "./headers.h"

int pop_front (struct dbl_queue* q)
{
    if (q->front == q->back) { // singleton list case
        int data = q->front->data;
        free_node(q->front);
        q->front = 0;
        q->back = 0;
        
        return data;
    } else {
        struct node *front = q->front;
        int data = front->data;
        front->next->prev = 0;
        q->front = front->next;
        free_node(front);

        return data;
    }
}