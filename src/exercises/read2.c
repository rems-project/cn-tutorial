unsigned read (unsigned *p)
/*@ requires take P = Owned<unsigned>(p);
    ensures take P_post = Owned<unsigned>(p);
            return == P;
            P_post == P;
@*/
{
  return *p;
}
