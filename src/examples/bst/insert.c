#include "./headers.h"
#include "create_node.c"
// inserts a new node into binary tree

/* FILL IN CN FUNCTION SPEC HERE */
/* --BEGIN-- */
/*@ 
function [rec] (datatype Tree) insert (datatype Tree sapling, i32 value)
{
    match sapling 
    {
        Leaf{} => 
        {
            Node{Left: Leaf{}, Data: value, Right: Leaf{}}
        }
        Node{Left: l, Data: dat, Right: r} => 
        {

            ((value < dat) ? Node {Left: insert(l, value), Data: dat, Right: r} :
            Node {Left: l, Data: dat, Right: insert(r, value)})
        }
    }
}
@*/
/* --END-- */

struct node* node_insert(struct node* t, int value)
/* FILL IN HERE */
/* --BEGIN-- */
/*@ requires take T1 = Tree_At(t);
    ensures take ret = Tree_At(return);  
                 ret == insert(T1,value);
                 T1 != Leaf{} implies get_data(ret) == get_data(T1);
                !is_null(return);  
@*/
/* --END-- */
{
    /* --BEGIN-- */
    /*@ unfold insert(Leaf{}, value); @*/
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
