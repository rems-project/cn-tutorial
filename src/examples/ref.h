// ref.h

unsigned int *ref (unsigned int v)
/*@ trusted
    ensures take vr = Owned(return);
            vr == v
@*/
{}
