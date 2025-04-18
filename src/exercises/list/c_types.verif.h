extern struct sllist *malloc__sllist();
/*@ spec malloc__sllist();
    requires true;
    ensures take R = W<struct sllist>(return);
@*/

extern void free__sllist (struct sllist *p);
/*@ spec free__sllist(pointer p);
    requires take P = W<struct sllist>(p);
    ensures true;
@*/

