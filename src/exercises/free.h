extern void freeInt (int *p);
/*@ spec freeInt(pointer p);
    requires take P = W<int>(p);
    ensures true;
@*/


extern void freeUnsignedInt (unsigned int *p);
/*@ spec freeUnsignedInt(pointer p);
    requires take P = W<unsigned int>(p);
    ensures true;
@*/

