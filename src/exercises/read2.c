unsigned int read (unsigned int *p)
/*@ requires take P = RW<unsigned int>(p);
    ensures take P_post = RW<unsigned int>(p);
            return == P;
            P_post == P;
@*/
{
  return *p;
}
