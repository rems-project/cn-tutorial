void transfer (unsigned int *p, unsigned int *q)
/* --BEGIN-- */
/*@ requires take n1 = Owned(p);
             take m1 = Owned(q);
    ensures  take n2 = Owned(p);
             take m2 = Owned(q);
             n2 == n1 + m1;
             m2 == 0u32;
@*/
/* --END-- */
{
  unsigned int n = *p;
  unsigned int m = *q;
  unsigned int s = n + m;
  *p = s;
  *q = 0;
}

int main()
/*@ trusted; @*/
{
    unsigned int x = 5;
    unsigned int y = 11;
    transfer(&x, &y);
    /*@ assert(y == 0u32); @*/
    /*@ assert(x == 16u32); @*/
}
