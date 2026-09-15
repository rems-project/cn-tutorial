// Increment two different pointers (same as above)
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

// Increment the same pointer twice
void incr2b (unsigned int *p, unsigned int *q)
/*@ requires take P = RW<unsigned int>(p);
	     P+2 <= MAXu32();
             ptr_eq(q,p);
    ensures take P_post = RW<unsigned int>(p);
            ptr_eq(q,p);
            P_post == P + 2;
@*/
{
  unsigned int n = *p;
  unsigned int m = n+1;
  *p = m;
  n = *q;
  m = n+1;
  *q = m;
}

void call_both (unsigned int *p, unsigned int *q)
/*@ requires take pv = RW<unsigned int>(p);
             take qv = RW<unsigned int>(q);
	     pv+3 <= MAXu32();
	     qv+1 <= MAXu32();
    ensures take pv_ = RW<unsigned int>(p);
            take qv_ = RW<unsigned int>(q);
            pv_ == pv + 3;
            qv_ == qv + 1;
@*/
{
  incr2a(p, q);   // increment two different pointers
  incr2b(p, p);   // increment the same pointer twice
}
