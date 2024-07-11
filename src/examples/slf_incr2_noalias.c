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

int main()
{
    unsigned int x = 5;
    unsigned int y = 11;
    incr2a(&x, &y);
    /*@ assert (x == 6u32); @*/
    /*@ assert (y == 12u32); @*/

    // uncomment for failure
    // incr2a(&x,&x);
    // incr2a(&y,&y);
}
