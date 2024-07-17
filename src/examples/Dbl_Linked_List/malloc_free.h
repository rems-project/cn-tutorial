extern struct node *malloc_node();
/*@ spec malloc_node();
    requires true;
    ensures take u = Block<struct node>(return);
            !ptr_eq(return,NULL);
@*/ 

extern void free_node (struct node *p);
/*@ spec free_node(pointer p);
    requires take u = Block<struct node>(p);
    ensures true;
@*/