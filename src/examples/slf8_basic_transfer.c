void transfer (unsigned int *p, unsigned int *q)
/* --BEGIN-- */
/*@ requires take P = Owned(p);
             take Q = Owned(q);
    ensures  take P_post = Owned(p);
             take Q_post = Owned(q);
             P_post == P + Q;
             Q_post == 0u32;
@*/
/* --END-- */
{
  unsigned int n = *p;
  unsigned int m = *q;
  unsigned int s = n + m;
  *p = s;
  *q = 0;
}
