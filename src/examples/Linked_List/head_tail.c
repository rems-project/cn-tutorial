#include "headers.h"

// TODO: currently the correctness checks ensure that the list is 
// unchanged, but I would also like to specify that the function
// correctly finds the head or tail, respectively.

struct node *find_head_aux(struct node *n)
/*@ requires !is_null(n);
             take node = Owned<struct node>(n);
             take L = Own_Backwards(node.prev, n, node);
    ensures take node_ = Owned<struct node>(n);
            take L_ = Own_Backwards(node_.prev, n, node_);
            node == node_;
            L == L_;
@*/
{
    /*@ split_case(is_null(n)); @*/
    /*@ split_case(is_null((*n).prev)); @*/
    if (n->prev == 0)
    {
        return n;
    } else {
        /*@ split_case(is_null((*(*n).prev).prev)); @*/
        return find_head_aux(n->prev);
    }
}

// Takes any node in the list and returns the head of the list
// TODO: correctness check
struct node *find_head(struct node *n)
/*@ requires take L = Dll_at(n);
    ensures  take L_ = Dll_at(n);
             L == L_;
@*/
{
   /*@ split_case(is_null(n)); @*/
    if (n == 0)
    {
        return 0;
    } else {
        /*@ split_case(is_null((*n).prev)); @*/
        return find_head_aux(n);
    }
}


struct node *find_tail_aux(struct node *n)
/*@ requires !is_null(n);
             take node = Owned<struct node>(n);
             take L = Own_Forwards(node.next, n, node);
    ensures take node_ = Owned<struct node>(n);
            take L_ = Own_Forwards(node_.next, n, node_);
            node == node_;
            L == L_;
@*/
{
    /*@ split_case(is_null(n)); @*/
    /*@ split_case(is_null((*n).next)); @*/
    if (n->next == 0)
    {
        return n;
    } else {
        /*@ split_case(is_null((*(*n).next).next)); @*/
        return find_tail_aux(n->next);
    }
}

// Takes any node in the list and returns the tail of the list
// TODO: correctness check
struct node *findTail(struct node *n)
/*@ requires take L = Dll_at(n);
    ensures  take L_ = Dll_at(n);
             L == L_;
@*/
{
   /*@ split_case(is_null(n)); @*/
    if (n == 0)
    {
        return 0;
    } else {
        /*@ split_case(is_null((*n).next)); @*/
        return find_tail_aux(n);
    }
}