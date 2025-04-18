// Defines structure of Binary Tree Nodes
// Defines the specs for allocating and freeing the Nodes

struct node {
    int data;
    struct node* left;
    struct node* right;
};

extern struct node* malloc_node();
/*@ spec malloc_node();
    requires true;
    ensures take R = W<struct node>(return);
            !ptr_eq(return, NULL);
@*/ 

extern void freenode (struct node *t);
/*@ spec freenode(pointer t);
    requires take R = W<struct node>(t);
    ensures true;
@*/
