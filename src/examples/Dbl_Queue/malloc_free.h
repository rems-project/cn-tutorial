extern struct dbl_queue *malloc_dbl_queue();
/*@ spec malloc_dbl_queue();
    requires true;
    ensures take u = Block<struct dbl_queue>(return);
            !ptr_eq(return,NULL);
@*/ 

extern void free_dbl_queue (struct dbl_queue *p);
/*@ spec free_dbl_queue(pointer p);
    requires take u = Block<struct dbl_queue>(p);
    ensures true;
@*/

extern struct node *malloc_node();
/*@ spec malloc_node();
    requires true;
    ensures take u = Block<struct node>(return);
            !is_null(return);
@*/ 

extern void free_node (struct node *p);
/*@ spec free_node(pointer p);
    requires take u = Block<struct node>(p);
    ensures true;
@*/