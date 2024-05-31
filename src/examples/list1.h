struct int_list {
  int head;
  struct int_list* tail;
};

extern struct int_list *mallocIntList();
/*@ spec mallocIntList();
    requires true;
    ensures take u = Block<struct int_list>(return);
            return != NULL;
@*/ // 'return != NULL' should not be needed

extern void freeIntList (struct int_list *p);
/*@ spec freeIntList(pointer p);
    requires take u = Block<struct int_list>(p);
    ensures true;
@*/

