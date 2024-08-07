struct node_and_int {
  struct node* node;
  int data;
};

extern struct node_and_int *malloc_node_and_int();
/*@ spec malloc_node_and_int();
    requires true;
    ensures take u = Block<struct node_and_int>(return);
            !ptr_eq(return,NULL);
@*/ 

extern void free_node_and_int (struct node_and_int *p);
/*@ spec free_node_and_int(pointer p);
    requires take u = Block<struct node_and_int>(p);
    ensures true;
@*/