void incr_first (unsigned int *p, unsigned int *q)
/*@ requires take pv = Owned<unsigned int>(p)
    ensures take pv_ = Owned<unsigned int>(p);
            pv_ == pv + 1u32
@*/
{
  unsigned int n = *p;
  unsigned int m = n+1;
  *p = m;
}

void incr_first_frame (unsigned int *p, unsigned int *q)
/*@ requires take pv = Owned<unsigned int>(p);
             take qv = Owned<unsigned int>(q)
    ensures take pv_ = Owned<unsigned int>(p);
            take qv_ = Owned<unsigned int>(q);
            pv_ == pv + 1u32;
            qv_ == qv
@*/
{
  incr_first(p, q);
}
