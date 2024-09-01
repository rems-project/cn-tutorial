#include "./headers.h"
// counts the furthest distance from the root to the leaf node

/* FILL IN CN FUNCTION SPEC DEFINTION HERE */
/* --BEGIN-- */
/*@
function [rec] (u32) depth (datatype Tree sapling)
{
    match sapling 
    {
        Leaf {} => 
        {
            0u32
        }
        Node {Left: l, data: dat, right: r} => 
        {
            let left_b = depth(l);
            let right_b = depth(r);
            ((left_b > right_b) ? (1u32 + left_b) : (1u32 + right_b))
        }
    }
}
@*/
/* --END-- */

unsigned int node_depth(struct node* t)
/* FILL IN HERE */
/* --BEGIN-- */
/*@ requires take t1 = Tree_At(t);
    ensures take t2 = Tree_At(t);
                 t1 == t2;
             return == depth(t1);
@*/
/* --END-- */
{
    /* --BEGIN-- */
    /*@ unfold depth(t1); @*/
    /* --END-- */
    if (t == 0)
    {
        return 0;
    }
    else
    {
        unsigned int left_b = node_depth(t->left);
        unsigned int right_b = node_depth(t->right);
        return ((left_b > right_b) ? (1 + left_b) : (1 + right_b));
    }   
}
