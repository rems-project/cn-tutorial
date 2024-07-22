#include "tree.h"
// Extracts the members of a given tree node

int get_Tree_Data (struct TreeNode *t)
/* FILL IN HERE */
/* --BEGIN-- */
/*@ requires take v1 = IntTree(t);
    ensures  take v2 = IntTree(t);
                  v1 == v2;
            return == (is_null(t) ? 0i32 : get_data(v2)); @*/
/* --END-- */
{
    if (t)
    {
        return t->data;
    }
    else
    {
        return 0;
    }
}

struct TreeNode* get_Tree_Left (struct TreeNode *t)
/* FILL IN HERE */
/* --BEGIN-- */
/*@ requires take v1 = Owned<struct TreeNode>(t);
             take v1_left = Owned<struct TreeNode>(v1.left);
    ensures  take v2 = Owned<struct TreeNode>(t);
             take v2_left = Owned<struct TreeNode>(v2.left);
             v1 == v2 && v1_left == v2_left;
    ptr_eq(return, ((is_null(t)) ? (t) : (v1.left))); @*/
/* --END-- */
{
    if (t)
    {
        return t->left;
    }
    else
    {
        return 0;
    }
}

struct TreeNode* get_Tree_Right (struct TreeNode *t)
/* FILL IN HERE */
/* --BEGIN-- */
/*@ requires take v1 = Owned<struct TreeNode>(t);
             take v1_right = Owned<struct TreeNode>(v1.right);
    ensures  take v2 = Owned<struct TreeNode>(t);
             take v2_right = Owned<struct TreeNode>(v2.right);
             v1 == v2 && v1_right == v2_right;
    ptr_eq(return, ((is_null(t)) ? (t) : (v1.right))); @*/
/* --END-- */
{
    if (t)
    {
        return t->right;
    }
    else
    {
        return 0;
    }
}