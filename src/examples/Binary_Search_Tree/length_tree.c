#include "tree.h"
// Function which counts all the nodes in the tree

/* FILL IN CN FUNCTION SPEC DEFINTION HERE */
/* --BEGIN-- */
/*@
function [rec] (u32) length (datatype tree sapling)
{
    match sapling 
    {
        Tree_Nil {} => 
        {
            0u32
        }
        Tree_Cons {left: l, data: dat, right: r} => 
        {
            let left_b = length(l);
            let right_b = length(r);
            (1u32 + left_b + right_b)
        }
    }
}
@*/
/* --END-- */

unsigned int TreeNode_length(struct TreeNode* t)
/* FILL IN HERE */
/* --BEGIN-- */
/*@ requires take t1 = IntTree(t);
    ensures take t2 = IntTree(t);
                 t1 == t2;
             return == length(t1);
@*/
/* --END-- */
{
    /* --BEGIN-- */
    /*@ unfold length(t1); @*/
    /* --END-- */
    if (t == 0)
    {
        return 0;
    }
    else
    {
        unsigned int left_b = TreeNode_length(t->left);
        unsigned int right_b = TreeNode_length(t->right);
        return (1 + left_b + right_b);
    }   
}