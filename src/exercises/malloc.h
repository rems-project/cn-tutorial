extern int *mallocInt ();
/*@ spec mallocInt();
    requires true;
    ensures take R = Block<int>(return);
@*/

extern unsigned int *mallocUnsignedInt ();
/*@ spec mallocUnsignedInt();
    requires true;
    ensures take R = Block<unsigned int>(return);
@*/

