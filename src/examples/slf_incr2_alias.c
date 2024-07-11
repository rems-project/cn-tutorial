void incr2b (unsigned int *p, unsigned int *q)
/*@ requires take pv = Owned<unsigned int>(p);
             ptr_eq(q,p);
    ensures take pv_ = Owned<unsigned int>(p);
            ptr_eq(q,p);
            pv_ == pv + 2u32;
@*/
{
  unsigned int n = *p;
  unsigned int m = n+1;
  *p = m;
  n = *q;
  m = n+1;
  *q = m;
}

//#include "slf_incr2_noalias.c"

void incr2a (unsigned int *p, unsigned int *q)
/*@ requires take pv = Owned<unsigned int>(p);
             take qv = Owned<unsigned int>(q);
    ensures take pv_ = Owned<unsigned int>(p);
            take qv_ = Owned<unsigned int>(q);
            pv_ == pv + 1u32;
            qv_ == qv + 1u32;
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
             take qv = Owned<unsigned int>(q);
    ensures take pv_ = Owned<unsigned int>(p);
            take qv_ = Owned<unsigned int>(q);
            pv_ == pv + 3u32;
            qv_ == qv + 1u32;
@*/
{
  incr2a(p, q);
  incr2b(p, p);
}

int main()
/*@ trusted; @*/
{
    unsigned int x = 5;
    unsigned int y = 11;
    call_both(&x, &y);
    /*@ assert(x == 8u32); @*/
    /*@ assert(y == 12u32); @*/

    // uncomment for assertion failure
    // call_both(&y,&y);
    // call_both(&x, &x);
}
