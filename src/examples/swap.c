void swap (unsigned int *p, unsigned int *q)
/* --BEGIN-- */
/*@ requires take P = Owned<unsigned int>(p);
             take Q = Owned<unsigned int>(q);
    ensures  take P_post = Owned<unsigned int>(p);
             take Q_post = Owned<unsigned int>(q);
             P_post == Q && Q_post == P;
@*/
/* --END-- */
{
  unsigned int m = *p;
  unsigned int n = *q;
  *p = n;
  *q = m;
}
