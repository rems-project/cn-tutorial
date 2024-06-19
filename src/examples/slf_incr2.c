/*@
predicate { u32 pv, u32 qv } BothOwned (pointer p, pointer q)
{
  if (ptr_eq(p,q)) {
    take pv = Owned<unsigned int>(p);
    return {pv: pv, qv: pv};
  }
  else {
    take pv = Owned<unsigned int>(p);
    take qv = Owned<unsigned int>(q);
    return {pv: pv, qv: qv};
  }
}
@*/

void incr2 (unsigned int *p, unsigned int *q)
/*@ requires take vs = BothOwned(p,q);
    ensures take vs_ = BothOwned(p,q);
            ptr_eq (vs_.pv,
                    (!ptr_eq(p,q)) ? (vs.pv + 1u32) : (vs.pv + 2u32));
            ptr_eq (vs_.qv,
                    (!ptr_eq(p,q)) ? (vs.qv + 1u32) : vs_.pv);
@*/
{
  /*@ split_case ptr_eq(p,q); @*/
  unsigned int n = *p;
  unsigned int m = n+1;
  *p = m;
  n = *q;
  m = n+1;
  *q = m;
}

void call_both_better (unsigned int *p, unsigned int *q)
/*@ requires take pv = Owned<unsigned int>(p);
             take qv = Owned<unsigned int>(q);
             !ptr_eq(p,q);
    ensures take pv_ = Owned<unsigned int>(p);
            take qv_ = Owned<unsigned int>(q);
            pv_ == pv + 3u32;
            qv_ == qv + 1u32;
@*/
{
  incr2(p, q);
  incr2(p, p);
}
