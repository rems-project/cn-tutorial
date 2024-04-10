unsigned int *refUnsignedInt (unsigned int v)
/*@ trusted
    ensures take vr = Owned(return);
            vr == v
@*/
{}
