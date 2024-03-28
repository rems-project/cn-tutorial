void swap (unsigned int *p, unsigned int *q)
/*@ requires take v = Owned<unsigned int>(p);
             take w = Owned<unsigned int>(q)
    ensures  take v2 = Owned<unsigned int>(p);
             take w2 = Owned<unsigned int>(q);
             v2 == w && w2 == v
@*/
{
  unsigned int m = *p;
  unsigned int n = *q;
  *p = n;
  *q = m;
}

struct upoint { unsigned int x; unsigned int y; };

void transpose2 (struct upoint *p)
--BEGIN--
/*@ requires take s = Owned<struct upoint>(p)
    ensures take s2 = Owned<struct upoint>(p);
            s2.x == s.y;
            s2.y == s.x @*/
{
  swap(&p->x, &p->y);
}
--END--
