#include "./headers.h"
#include "create_node.c"
// inserts a new node into binary tree

/* FILL IN CN FUNCTION SPEC HERE */
/* --BEGIN-- */
/*@ 
function [rec] (datatype tree) insert (datatype tree sapling, i32 value)
{
    match sapling 
    {
        Tree_Nil{} => 
        {
            Tree_Cons{left: Tree_Nil{}, data: value, right: Tree_Nil{}}
        }
        Tree_Cons{left: l, data: dat, right: r} => 
        {

            ((value < dat) ? Tree_Cons {left: insert(l, value), data: dat, right: r} :
            Tree_Cons {left: l, data: dat, right: insert(r, value)})
        }
    }
}
@*/
/* --END-- */

struct node* node_insert(struct node* t, int value)
/* FILL IN HERE */
/* --BEGIN-- */
/*@ requires take T1 = IntTree(t);
    ensures take ret = IntTree(return);  
                 ret == insert(T1,value);
                 T1 != Tree_Nil{} implies get_data(ret) == get_data(T1);
                !is_null(return);  
@*/
/* --END-- */
{
    /* --BEGIN-- */
    /*@ unfold insert(Tree_Nil{}, value); @*/
    /*@ unfold insert(T1, value); @*/
    /* --END-- */
    if (t == 0)
    {
        struct node* add = node_create_node(value);
        return add;
    }
    else
    {
        if (value < t->data)
        {
            t->left = node_insert(t->left, value);
            return t;
            
        }   
        else
        {
            t->right = node_insert(t->right, value);
            return t;
        }
    }
}
