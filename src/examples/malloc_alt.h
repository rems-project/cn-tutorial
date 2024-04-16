// malloc.h

extern int *mallocInt ();
/*@ spec mallocInt()
    requires true
    ensures take v = Block<int>(return)
@*/


extern unsigned int *mallocUnsignedInt ();
/*@ spec mallocUnsignedInt()
    requires true
    ensures take v = Block<unsigned int>(return)
@*/

