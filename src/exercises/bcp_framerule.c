void incr_first (unsigned int *p, unsigned int *q)
/*@ requires take pv = RW<unsigned int>(p);
    ensures take pv_ = RW<unsigned int>(p);
            pv_ == pv + 1u32;
@*/
{
  unsigned int n = *p;
  unsigned int m = n+1;
  *p = m;
}

void incr_first_frame (unsigned int *p, unsigned int *q)
/*@ requires take pv = RW<unsigned int>(p);
             take qv = RW<unsigned int>(q);
    ensures take pv_ = RW<unsigned int>(p);
            take qv_ = RW<unsigned int>(q);
            pv_ == pv + 1u32;
            qv_ == qv;
@*/
{
  incr_first(p, q);
}
