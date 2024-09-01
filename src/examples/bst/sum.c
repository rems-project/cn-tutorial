#include "./headers.h"
// Sums up the data values of the nodes of the binary tree

/* FILL IN CN FUNCTION SPEC DEFINTION HERE */
/* --BEGIN-- */
/*@
function [rec] (u32) sum(datatype Tree sapling)
{
    match sapling 
    {
        Leaf {} => 
        {
            0u32
        }
        Node {left: l, data: dat, right: r} => 
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
/*@ requires take t1 = Tree_At(t);
    ensures  take t2 = Tree_At(t);
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