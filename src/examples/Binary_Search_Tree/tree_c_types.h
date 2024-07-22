// Defines structure of Binary Tree Nodes
// Defines the specs for allocating and freeing the Nodes

struct TreeNode {
    int data;
    struct TreeNode* left;
    struct TreeNode* right;
};

extern struct TreeNode* mallocTreeNode();
/*@ spec mallocTreeNode();
    requires true;
    ensures take u = Block<struct TreeNode>(return);
            !ptr_eq(return, NULL);
@*/ 

extern void freeTreeNode (struct TreeNode *t);
/*@ spec freeTreeNode(pointer t);
    requires take u = Block<struct TreeNode>(t);
    ensures true;
@*/