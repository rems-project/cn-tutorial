// Increment two different pointers (same as above)
void incr2a (unsigned int *p, unsigned int *q)
/*@ requires take P = RW<unsigned int>(p);
             take Q = RW<unsigned int>(q);
    ensures take P_post = RW<unsigned int>(p);
            take Q_post = RW<unsigned int>(q);
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

// Increment the same pointer twice
void incr2b (unsigned int *p, unsigned int *q)
/*@ requires take P = RW<unsigned int>(p);
             ptr_eq(q,p);
    ensures take P_post = RW<unsigned int>(p);
            ptr_eq(q,p);
            P_post == P + 2u32;
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
    ensures take pv_ = RW<unsigned int>(p);
            take qv_ = RW<unsigned int>(q);
            pv_ == pv + 3u32;
            qv_ == qv + 1u32;
@*/
{
  incr2a(p, q);   // increment two different pointers
  incr2b(p, p);   // increment the same pointer twice
}
