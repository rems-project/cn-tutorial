#include "./headers.h"
#include "./constructors.h"
// takes in binary tree, Returns copy of it

struct node* node_copy (struct node* t)
/* FILL IN HERE */
/* --BEGIN-- */
/*@ requires take T1 = IntTree(t);
    ensures  take T1_ = IntTree(t);
             take T2  = IntTree(return);
                  T1 == T1_;
                  T1 == T2;
@*/
/* --END-- */
{
    if (t == 0)
    {
        return node_nil();
    }
    else
    {
        struct node* new_left = node_copy(t->left);
        struct node* new_right = node_copy(t->right);
        return node_cons_both(t->data, new_left, new_right);
    }
}