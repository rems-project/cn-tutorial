void incr2a (unsigned int *p, unsigned int *q)
/*@ requires take P = Owned<unsigned int>(p);
             take Q = Owned<unsigned int>(q);
    ensures take P_post = Owned<unsigned int>(p);
            take Q_post = Owned<unsigned int>(q);
            P_post == P + 1u32;
            Q_post == Q + 1u32;
@*/
{
  unsigned int n = *p;
  unsigned int m = n+1;
  *p = m;
  n = *q;
  m = n+1;
  *q = m;
}

