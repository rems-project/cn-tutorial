// #include "slf4_basic_incr_two.c"

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


void incr_two (unsigned int *p, unsigned int *q)
/*@ requires take n1 = Owned(p);
             take m1 = Owned(q);
    ensures take n2 = Owned(p);
            take m2 = Owned(q);
            n2 == n1 + 1u32;
            m2 == m1 + 1u32;
@*/
{
  incr(p);
  incr(q);
}



void aliased_call (unsigned int *p)
/*@ requires take n1 = Owned(p); 
    ensures take n2 = Owned(p);
            n2 == n1 + 2u32; @*/
{
  incr_two(p, p);
}

int main()
/*@ trusted; @*/
{
    // uncomment for failure
    // unsigned int x = 5;
    // aliased_call(&x);
}
