#include "./headers.h"
// Sums up the data values of the nodes of the binary tree

/* FILL IN CN FUNCTION SPEC DEFINTION HERE */
/* --BEGIN-- */
/*@
function [rec] (u32) sum(datatype tree sapling)
{
    match sapling 
    {
        Tree_Nil {} => 
        {
            0u32
        }
        Tree_Cons {left: l, data: dat, right: r} => 
        {
            let rt_val = (u32) dat;
            let sum_lb = sum(l);
            let sum_rb = sum(r);
            (rt_val + sum_lb + sum_rb)
        }
    }
}
@*/
/* --END-- */

unsigned int node_sum(struct node* t)
/* FILL IN HERE */
/* --BEGIN-- */
/*@ requires take t1 = IntTree(t);
    ensures  take t2 = IntTree(t);
                 t1 == t2;
             return == sum(t1);
@*/
/* --END-- */
{   
    /* --BEGIN-- */
    /*@ unfold sum(t1); @*/
    /* --END-- */
    if (t == 0)
    {
        return 0;
    }
    else
    {
        unsigned int sum_lb = node_sum(t->left);
        unsigned int sum_rb = node_sum(t->right);
        unsigned int root_val = t->data;
        return (root_val + sum_lb + sum_rb);
    }   
}