extern void freeInt (int *p);
/*@ spec freeInt(pointer p);
    requires take P = Block<int>(p);
    ensures true;
@*/


extern void freeUnsignedInt (unsigned int *p);
/*@ spec freeUnsignedInt(pointer p);
    requires take P = Block<unsigned int>(p);
    ensures true;
@*/

