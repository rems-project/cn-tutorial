#include "./headers.h"
// Initializes new node with value given as its argument

struct node* node_create_node(int value)
/* FILL IN HERE */
/* --BEGIN-- */
/*@ ensures take T = IntTree(return);
        T == Tree_Cons {left: Tree_Nil{}, data: value, right: Tree_Nil{}};
        !is_null(return);
        get_data(T) == value;
@*/
/* --END-- */
{
    struct node* node = malloc_node();
    node->data = value;
    node->left = 0;
    node->right = 0;
    return node;
}