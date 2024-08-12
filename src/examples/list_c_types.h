struct sllist {
  int head;
  struct sllist* tail;
};

extern struct sllist *malloc_sllist();
/*@ spec malloc_sllist();
    requires true;
    ensures take u = Block<struct sllist>(return);
@*/

extern void free_sllist (struct sllist *p);
/*@ spec free_sllist(pointer p);
    requires take u = Block<struct sllist>(p);
    ensures true;
@*/

