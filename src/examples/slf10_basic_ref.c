extern unsigned int *refUnsignedInt (unsigned int v);
/*@ spec refUnsignedInt(u32 v);
    requires true;
    ensures take vr = RW(return);
            vr == v;
@*/

