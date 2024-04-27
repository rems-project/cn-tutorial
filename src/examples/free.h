// free.h

extern void freeInt (int *p);
/*@ spec freeInt(pointer p)
    requires take v = Block<int>(p);
    ensures true;
@*/


extern void freeUnsignedInt (unsigned int *p);
/*@ spec freeUnsignedInt(pointer p)
    requires take v = Block<unsigned int>(p);
    ensures true;
@*/

