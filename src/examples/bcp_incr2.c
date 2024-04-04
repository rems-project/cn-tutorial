/* First, let's deal with the "normal" case where p and q do not alias... */

void incr2a (unsigned int *p, unsigned int *q)
/*@ requires take pv = Owned<unsigned int>(p);
             take qv = Owned<unsigned int>(q)
    ensures take pv_ = Owned<unsigned int>(p);
            take qv_ = Owned<unsigned int>(q);
            pv_ == pv + 1u32;

@*/
{
  unsigned int n = *p;
  unsigned int m = n+1;
  *p = m;
  n = *q;
  m = n+1;
  *q = m;
}

/* Now, what if they do alias?  The clunky solution is to write a
   whole 'nother version of incr2 with a different spec... */

void incr2b (unsigned int *p, unsigned int *q)
/*@ requires take pv = Owned<unsigned int>(p);
             q == p
    ensures take pv_ = Owned<unsigned int>(p);
            q == p;
            pv_ == pv + 2u32
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
/*@ requires take pv = Owned<unsigned int>(p);
             take qv = Owned<unsigned int>(q)
    ensures take pv_ = Owned<unsigned int>(p);
            take qv_ = Owned<unsigned int>(q);
            pv_ == pv + 3u32;
            qv_ == qv + 1u32
@*/
{
  incr2a(p, q);
  incr2b(p, p);
}

/* But this is horrible.  Much better is to define a predicate to use
   in the pre- and postconditions that captures both cases together: */

/*@
predicate { u32 pv, u32 qv } BothOwned (pointer p, pointer q)
{
  if (p == q) {
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
/*@ requires take vs = BothOwned(p,q)
    ensures take vs_ = BothOwned(p,q);
            vs_.pv == ((p != q) ? (vs.pv + 1u32) : (vs.pv + 2u32));
            vs_.qv == ((p != q) ? (vs.qv + 1u32) : vs_.pv)
@*/
{
  /*@ split_case p == q; @*/
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
             p != q
    ensures take pv_ = Owned<unsigned int>(p);
            take qv_ = Owned<unsigned int>(q);
            pv_ == pv + 3u32;
            qv_ == qv + 1u32
@*/
{
  incr2(p, q);
  incr2(p, p);
}
