void swap (unsigned int *p, unsigned int *q)
/* --BEGIN-- */
/*@ requires take v = Owned<unsigned int>(p);
             take w = Owned<unsigned int>(q);
    ensures  take v2 = Owned<unsigned int>(p);
             take w2 = Owned<unsigned int>(q);
             v2 == w && w2 == v;
@*/
/* --END-- */
{
  unsigned int m = *p;
  unsigned int n = *q;
  *p = n;
  *q = m;
}

int main()
/*@ trusted; @*/
{
    unsigned int x = 5;
    unsigned int y = 11;
    swap(&x, &y);
    /*@ assert (y == 5u32); @*/
    /*@ assert (x == 11u32); @*/

    // uncomment for failure
    // swap(&x, &x);
    // swap(&y, &x);
}

