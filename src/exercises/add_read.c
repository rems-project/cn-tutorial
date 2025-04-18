unsigned int add (unsigned int *p, unsigned int *q)
/*@ requires take P = RW<unsigned int>(p);
             take Q = RW<unsigned int>(q);
    ensures take P_post = RW<unsigned int>(p);
            take Q_post = RW<unsigned int>(q);
            P == P_post && Q == Q_post;
            return == P + Q;
@*/
{
  unsigned int m = *p;
  unsigned int n = *q;
  return m+n;
}
