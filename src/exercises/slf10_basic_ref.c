extern unsigned int *refUnsignedInt (unsigned int v);
/*@ spec refUnsignedInt(integer v);
    requires true;
    ensures take vr = RW(return);
            vr == v;
@*/

