extern int *malloc__int ();
/*@ spec malloc__int();
    requires true;
    ensures take R = W<int>(return);
@*/

extern unsigned int *malloc__unsigned_int ();
/*@ spec malloc__unsigned_int();
    requires true;
    ensures take R = W<unsigned int>(return);
@*/

