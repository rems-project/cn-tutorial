void incr2a (unsigned int *p, unsigned int *q)
/*@ requires take P = RW<unsigned int>(p);
             take Q = RW<unsigned int>(q);
	     P < MAXu32();
	     Q < MAXu32();
    ensures take P_post = RW<unsigned int>(p);
            take Q_post = RW<unsigned int>(q);
            P_post == P + 1;
            Q_post == Q + 1;
@*/
{
  unsigned int n = *p;
  unsigned int m = n+1;
  *p = m;
  n = *q;
  m = n+1;
  *q = m;
}

