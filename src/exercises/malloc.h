extern int *mallocInt ();
/*@ spec mallocInt();
    requires true;
    ensures take R = W<int>(return);
@*/

extern unsigned int *mallocUnsignedInt ();
/*@ spec mallocUnsignedInt();
    requires true;
    ensures take R = W<unsigned int>(return);
@*/

