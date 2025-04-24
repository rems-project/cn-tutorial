#include "./headers.verif.h"
// deallocates all the nodes in the binary tree

void node_free_tree (struct node* t)
/* FILL IN HERE */
/* --BEGIN-- */
/*@  requires take v1 = Tree_At(t); @*/
/* --END-- */
{
    if (t == 0)
    {
        return;
    } 
    else
    {
        node_free_tree(t->right);
        node_free_tree(t->left);
        freenode(t);
    }
}