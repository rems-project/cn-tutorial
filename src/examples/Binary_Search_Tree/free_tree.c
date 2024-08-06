#include "tree.h"
// deallocates all the nodes in the binary tree

void TreeNode_free_tree (struct TreeNode* t)
/* FILL IN HERE */
/* --BEGIN-- */
/*@  requires take v1 = IntTree(t); @*/
/* --END-- */
{
    if (t == 0)
    {
        return;
    } 
    else
    {
        TreeNode_free_tree(t->right);
        TreeNode_free_tree(t->left);
        freeTreeNode(t);
    }
}