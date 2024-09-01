struct dllist_and_int {
  struct dllist* dllist;
  int data;
};

extern struct dllist_and_int *malloc__dllist_and_int();
/*@ spec malloc__dllist_and_int();
    requires true;
    ensures take u = Block<struct dllist_and_int>(return);
            !ptr_eq(return,NULL);
@*/ 

extern void free__dllist_and_int (struct dllist_and_int *p);
/*@ spec free__dllist_and_int(pointer p);
    requires take u = Block<struct dllist_and_int>(p);
    ensures true;
@*/