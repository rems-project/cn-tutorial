unsigned int add (unsigned int *p, unsigned int *q)
/*@ requires take P = Owned<unsigned int>(p);
             take Q = Owned<unsigned int>(q);
    ensures take P_post = Owned<unsigned int>(p);
            take Q_post = Owned<unsigned int>(q);
            P == P_post && Q == Q_post;
            return == P + Q;
@*/
{
  unsigned int m = *p;
  unsigned int n = *q;
  return m+n;
}
