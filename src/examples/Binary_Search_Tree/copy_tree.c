#include "tree.h"
#include "tree_constructors.h"
// takes in binary tree, Returns copy of it

struct TreeNode* TreeNode_copy (struct TreeNode* t)
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
        return TreeNode_nil();
    }
    else
    {
        struct TreeNode* new_left = TreeNode_copy(t->left);
        struct TreeNode* new_right = TreeNode_copy(t->right);
        return TreeNode_cons_both(t->data, new_left, new_right);
    }
}