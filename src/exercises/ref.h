extern unsigned int *refUnsignedInt (unsigned int v);
/*@ spec refUnsignedInt(u32 v);
    requires true;
    ensures take R = RW(return);
            R == v;
@*/

extern int *refInt (int v);
/*@ spec refInt(i32 v);
    requires true;
    ensures take R = RW(return);
            R == v;
@*/

