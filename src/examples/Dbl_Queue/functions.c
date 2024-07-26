#include "./predicates.c"
extern struct dbl_queue *malloc_dbl_queue();
/*@ spec malloc_dbl_queue();
    requires true;
    ensures take u = Block<struct dbl_queue>(return);
            !ptr_eq(return,NULL);
@*/ 

extern void free_dbl_queue (struct dbl_queue *p);
/*@ spec free_dbl_queue(pointer p);
    requires take u = Block<struct dbl_queue>(p);
    ensures true;
@*/

extern struct node *malloc_node();
/*@ spec malloc_node();
    requires true;
    ensures take u = Block<struct node>(return);
            !is_null(return);
@*/ 

extern void free_node (struct node *p);
/*@ spec free_node(pointer p);
    requires take u = Block<struct node>(p);
    ensures true;
@*/

struct dbl_queue *empty_dbl_queue()
/*@ ensures 
        !is_null(return);
        take ret = Dbl_Queue_Fwd_At(return);
        ret == Seq_Nil{};
@*/
{
  struct dbl_queue *q = malloc_dbl_queue();
  q->front = 0;
  q->back = 0;
  return q;
}

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
    /*@ split_case(ptr_eq((*q).front, (*q).back)); @*/

    if (q->front != 0) {
        /*@ split_case(ptr_eq((*(*q).front).next, (*q).back)); @*/
        q->front->prev = new_node;
        q->front = new_node;

    } else {
        // in this case, the queue is empty
        q->back = new_node;
        q->front = new_node;
    }
}


int pop_front (struct dbl_queue* q)
/*@ requires (!is_null(q));
             take Before = Dbl_Queue_Fwd_At(q);
             Before != Seq_Nil{};
    ensures  take After = Dbl_Queue_Fwd_At(q);
             After == tl(Before);
             hd(Before) == return;
@*/
{
    /*@ split_case(is_null(q->back)); @*/
    /*@ assert(!is_null(q->front)); @*/

    if (q->front == q->back) { // singleton list case
        int data = q->front->data;
        free_node(q->front);
        q->front = 0;
        q->back = 0;
        return data;

    } else {
        /*@ split_case(ptr_eq((*(*q).front).next, (*q).back)); @*/
        struct node *front = q->front;
        int data = front->data;
        front->next->prev = 0;
        q->front = front->next;
        free_node(front);

        /*@ split_case(ptr_eq((*(*q).front).next, (*q).back)); @*/
        return data;
    }
}

// Given a dbl queue pointer, inserts a new node
// to the back of the list
void push_back (struct dbl_queue* q, int element)
/*@ requires (!is_null(q));
             take Before = Dbl_Queue_Bwd_At(q);
    ensures  take After = Dbl_Queue_Bwd_At(q);
             After == Seq_Cons{head: element, tail: Before};
            //  Before == snoc(After, element); // reverse???
@*/
{
    struct node *new_node = malloc_node();
    new_node->data = element;
    new_node->next = 0;
    new_node->prev = q->back;
    /*@ split_case(ptr_eq((*q).front, (*q).back)); @*/

    if (q->back != 0) {
        /*@ split_case(ptr_eq((*(*q).back).prev, (*q).front)); @*/
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

int pop_back (struct dbl_queue* q)
/*@ requires (!is_null(q));
             take Before = Dbl_Queue_Bwd_At(q);
             Before != Seq_Nil{};
    ensures  take After = Dbl_Queue_Bwd_At(q);
             After == tl(Before);
             hd(Before) == return;
@*/
{
    /*@ split_case(is_null(q->back)); @*/
    /*@ assert(!is_null(q->front)); @*/

    if (q->front == q->back) { // singleton list case
        int data = q->back->data;
        free_node(q->back);
        q->front = 0;
        q->back = 0;
        return data;

    } else {
        /*@ split_case(ptr_eq((*(*q).back).prev, (*q).front)); @*/
        struct node *back = q->back;
        int data = back->data;
        back->prev->next = 0;
        q->back = back->prev;
        free_node(back);

        /*@ split_case(ptr_eq((*(*q).back).prev, (*q).front)); @*/
        return data;
    }
}