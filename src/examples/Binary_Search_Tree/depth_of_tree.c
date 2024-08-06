#include "tree.h"
// counts the furthest distance from the root to the leaf node

/* FILL IN CN FUNCTION SPEC DEFINTION HERE */
/* --BEGIN-- */
/*@
function [rec] (u32) depth (datatype tree sapling)
{
    match sapling 
    {
        Tree_Nil {} => 
        {
            0u32
        }
        Tree_Cons {left: l, data: dat, right: r} => 
        {
            let left_b = depth(l);
            let right_b = depth(r);
            ((left_b > right_b) ? (1u32 + left_b) : (1u32 + right_b))
        }
    }
}
@*/
/* --END-- */

unsigned int TreeNode_depth(struct TreeNode* t)
/* FILL IN HERE */
/* --BEGIN-- */
/*@ requires take t1 = IntTree(t);
    ensures take t2 = IntTree(t);
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
        unsigned int left_b = TreeNode_depth(t->left);
        unsigned int right_b = TreeNode_depth(t->right);
        return ((left_b > right_b) ? (1 + left_b) : (1 + right_b));
    }   
}