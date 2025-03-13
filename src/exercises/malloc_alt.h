extern int *mallocInt ();
/*@ spec mallocInt()
    requires true
    ensures take v = W<int>(return)
@*/


extern unsigned int *mallocUnsignedInt ();
/*@ spec mallocUnsignedInt()
    requires true
    ensures take v = W<unsigned int>(return)
@*/

