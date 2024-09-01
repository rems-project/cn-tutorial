#include "./headers.h"
// returns true (1u32) or false (u32), if value is an node in the binary tree

/* FILL IN CN FUNCTION SPEC DEFINTION HERE */
/* --BEGIN-- */
/*@
function [rec] (u32) exists(datatype tree sapling, i32 value)
{
    match sapling 
    {
        Tree_Nil {} => 
        {
            0u32
        }
        Tree_Cons {left: l, data: dat, right: r} =>
        {   
            let lb_exist = exists(l, value);
            let rb_exist = exists(r, value);  
            ((value == dat)
                ? 1u32
                : ((value < dat) ? lb_exist  : rb_exist))
        }
    }
}
@*/
/* --END-- */

typedef enum { false, true } bool;

bool node_containsValue (struct node* t, int value)
/* FILL IN HERE */
/* --BEGIN-- */
/*@ requires take t1 = IntTree(t);
    ensures  take t2 = IntTree(t);
                  t1 == t2;
            return == exists(t1, value);
@*/
/* --END-- */
{   
    /* --BEGIN-- */
    /*@ unfold exists(t1, value); @*/
    /* --END-- */
    if (t == 0)
    {
        return false;
    }
    else
    {
        
        if (t->data == value)
        {
            return true;
        }
        else
        {
            if (value < t->data)
            {      
                return node_containsValue(t->left, value);
            }
            else
            {
                return node_containsValue(t->right, value);
            }
        }
    }
}