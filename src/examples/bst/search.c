#include "./headers.h"
// Searches for a node with the given value in the binary Tree

/* FILL IN CN FUNCTION SPEC DEFINTION HERE */
/* --BEGIN-- */
/*@
function [rec] (datatype Tree) search(datatype Tree sapling, i32 value)
{
    match sapling 
    {
        Leaf {} => 
        {
            Leaf{}
        }
        Node {Left: l, data: dat, right: r} =>
        {
            ((value == dat) ? sapling :
            ((value < dat) ? search(l, value) : search(r, value)))
        }
    }
}
@*/
/* --END-- */

struct node* node_search(struct node* t, int value)
/* FILL IN HERE */
/* --BEGIN-- */
/*@ requires take t1 = Tree_At(t);
    ensures  take t2 = Tree_At(t);
                  t1 == t2;
                  let ret = search(t1, value);
                  (ret == Leaf{} ? is_null(return) : get_data(ret) == value);                
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
                return node_search(t->left, value);
            }
            else
            {
                return node_search(t->right, value);
            }
        }
    }
}