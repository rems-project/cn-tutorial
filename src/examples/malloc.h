int *mallocInt ()
/*@ trusted
    requires true
    ensures take v = Block<int>(return)
@*/
{}

unsigned int *mallocUnsignedInt ()
/*@ trusted
    requires true
    ensures take v = Block<unsigned int>(return)
@*/
{}
