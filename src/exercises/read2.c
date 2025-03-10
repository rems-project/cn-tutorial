unsigned int read (unsigned int *p)
/*@ requires take P = Owned<unsigned int>(p);
    ensures take P_post = Owned<unsigned int>(p);
            return == P;
            P_post == P;
@*/
{
  return *p;
}
