extern struct node *malloc__node();
/*@ spec malloc__node();
    requires true;
    ensures take u = Block<struct node>(return);
            !ptr_eq(return,NULL);
@*/ 

extern void free__node (struct node *p);
/*@ spec free__node(pointer p);
    requires take u = Block<struct node>(p);
    ensures true;
@*/