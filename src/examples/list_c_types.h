struct list_int {
  int head;
  struct list_int* tail;
};

extern struct list_int *malloc_list_int();
/*@ spec malloc_list_int();
    requires true;
    ensures take u = Block<struct list_int>(return);
@*/

extern void free_list_int (struct list_int *p);
/*@ spec free_list_int(pointer p);
    requires take u = Block<struct list_int>(p);
    ensures true;
@*/

