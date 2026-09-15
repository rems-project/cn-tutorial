extern unsigned int *refUnsignedInt (unsigned int v);
/*@ spec refUnsignedInt(integer v);
    requires true;
    ensures take R = RW(return);
            R == v;
@*/

extern int *refInt (int v);
/*@ spec refInt(integer v);
    requires true;
    ensures take R = RW(return);
            R == v;
@*/

