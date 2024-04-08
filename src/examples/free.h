// free.h

void freeInt (int *p)
/*@ trusted
    requires take v = Block<int>(p)
    ensures true
@*/
{}

void freeUnsignedInt (unsigned int *p)
/*@ trusted
    requires take v = Block<unsigned int>(p)
    ensures true
@*/
{}
