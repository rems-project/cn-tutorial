/*@
predicate { u32 P, u32 Q } BothOwned (pointer p, pointer q)
{
  if (ptr_eq(p,q)) {
    take PX = RW<unsigned int>(p);
    return {P: PX, Q: PX};
  }
  else {
    take PX = RW<unsigned int>(p);
    take QX = RW<unsigned int>(q);
    return {P: PX, Q: QX};
  }
}
@*/

void incr2(unsigned int *p, unsigned int *q)
/*@ requires take PQ = BothOwned(p,q);
    ensures take PQ_post = BothOwned(p,q);
            PQ_post.P == (!ptr_eq(p,q) ? (PQ.P + 1u32) : (PQ.P + 2u32));
            PQ_post.Q == (!ptr_eq(p,q) ? (PQ.Q + 1u32) : PQ_post.P);
@*/
{
  /*@ split_case ptr_eq(p,q); @*/
  unsigned int n = *p;
  unsigned int m = n + 1;
  *p = m;
  n = *q;
  m = n + 1;
  *q = m;
}

void call_both_better(unsigned int *p, unsigned int *q)
/*@ requires take P = RW<unsigned int>(p);
             take Q = RW<unsigned int>(q);
             !ptr_eq(p,q);
    ensures take P_post = RW<unsigned int>(p);
            take Q_post = RW<unsigned int>(q);
            P_post == P + 3u32;
            Q_post == Q + 1u32;
@*/
{
  incr2(p, q);
  incr2(p, p);
}
