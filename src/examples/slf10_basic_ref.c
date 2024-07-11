// TODO - REVISIT

unsigned int *refUnsignedInt (unsigned int v)
/*@ ensures take vr = Owned(return);
            vr == v;
@*/
{
    return 0;
}

int main()
/*@ trusted; @*/
{
    unsigned int v = 5;
    unsigned int *p = refUnsignedInt(v);
    /*@ assert (*p == 5u32); @*/
}
