void free_ (int *p)
/*@ trusted
    requires take v = Owned<int>(p) @*/
{}

