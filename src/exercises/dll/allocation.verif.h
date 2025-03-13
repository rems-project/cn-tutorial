extern struct dllist *malloc__dllist();
/*@ spec malloc__dllist();
    requires true;
    ensures take R = W<struct dllist>(return);
            !ptr_eq(return,NULL);
@*/ 

extern void free__dllist (struct dllist *p);
/*@ spec free__dllist(pointer p);
    requires take R = W<struct dllist>(p);
    ensures true;
@*/
