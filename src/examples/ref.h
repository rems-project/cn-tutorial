// ref.h

extern unsigned int *refUnsignedInt (unsigned int v);
/*@ spec refUnsignedInt(u32 v);
    requires true;
    ensures take vr = Owned(return);
            vr == v;
@*/


extern int *refInt (int v);
/*@ spec refInt(i32 v);
    requires true;
    ensures take vr = Owned(return);
            vr == v;
@*/

