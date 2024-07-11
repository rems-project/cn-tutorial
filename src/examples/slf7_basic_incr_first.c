// #include "slf0_basic_incr.c"

void incr (unsigned int *p)
/* --BEGIN-- */
/*@ requires take n1 = Owned<unsigned int>(p);
    ensures take n2 = Owned<unsigned int>(p);
            n2 == n1 + 1u32;
@*/
/* --END-- */
{
  unsigned int n = *p;
  unsigned int m = n+1;
  *p = m;
}


void incr_first(unsigned int *p, unsigned int *q)
/*@ requires take n1 = Owned(p);
             take m1 = Owned(q);
    ensures  take n2 = Owned(p);
             take m2 = Owned(q);
             n2 == n1 + 1u32;
             m2 == m1;
@*/
{
  incr(p);
}


void incr_first_(unsigned int *p, unsigned int *q)
/*@ requires take n1 = Owned(p);
    ensures  take n2 = Owned(p);
             n2 == n1 + 1u32;
@*/
{
  incr(p);
}

int main()
/*@ trusted; @*/
{
    unsigned int x = 5;
    unsigned int y = 11;
    incr_first_(&x, &y);
    /*@ assert (x == 6u32); @*/
    /*@ assert (y == 11u32); @*/
}
