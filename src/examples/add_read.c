unsigned int add (unsigned int *p, unsigned int *q)
/*@ requires take m = Owned<unsigned int>(p);
             take n = Owned<unsigned int>(q);
    ensures take m2 = Owned<unsigned int>(p);
            take n2 = Owned<unsigned int>(q);
            m == m2 && n == n2;
            return == m + n;
@*/
{
  unsigned int m = *p;
  unsigned int n = *q;
  return m+n;
}

int main()
/*@ trusted; @*/
{
    unsigned int x = 5;
    unsigned int y = 7;

    unsigned int res = add(&x, &y);
    /*@ assert (x == 5u32); @*/
    /*@ assert (y == 7u32); @*/
    /*@ assert (res == 12u32); @*/
}

