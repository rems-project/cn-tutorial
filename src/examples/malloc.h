int *mallocInt ()
/*@ trusted
    requires true
    ensures take v = Block<int>(return)
@*/
{}

int *mallocUnsignedInt ()
/*@ trusted
    requires true
    ensures take v = Block<int>(return)
@*/
{}
