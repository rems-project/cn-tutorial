#include "tree.h"
// Searches for a node with the given value in the binary tree

/* FILL IN CN FUNCTION SPEC DEFINTION HERE */
/* --BEGIN-- */
/*@
function [rec] (datatype tree) search(datatype tree sapling, i32 value)
{
    match sapling 
    {
        Tree_Nil {} => 
        {
            Tree_Nil{}
        }
        Tree_Cons {left: l, data: dat, right: r} =>
        {
            ((value == dat) ? sapling :
            ((value < dat) ? search(l, value) : search(r, value)))
        }
    }
}
@*/
/* --END-- */

struct TreeNode* TreeNode_search(struct TreeNode* t, int value)
/* FILL IN HERE */
/* --BEGIN-- */
/*@ requires take t1 = IntTree(t);
    ensures  take t2 = IntTree(t);
                  t1 == t2;
                  let ret = search(t1, value);
                  (ret == Tree_Nil{} ? is_null(return) : get_data(ret) == value);                
@*/
/* --END-- */
{   
    /* --BEGIN-- */
    /*@ unfold search(t1, value); @*/
    /* --END-- */
    if (t == 0)
    {
        
        return 0;
    }
    else
    {
        
        if (t->data == value)
        {
            return t;
        }
        else
        {
            if (value < t->data)
            {   
                return TreeNode_search(t->left, value);
            }
            else
            {
                return TreeNode_search(t->right, value);
            }
        }
    }
}