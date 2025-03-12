void swap (unsigned int *p, unsigned int *q)
/*@ requires take P = RW<unsigned int>(p);
             take Q = RW<unsigned int>(q);
    ensures  take P_post = RW<unsigned int>(p);
             take Q_post = RW<unsigned int>(q);
             P_post == Q && Q_post == P;
@*/
{
  unsigned int m = *p;
  unsigned int n = *q;
  *p = n;
  *q = m;
}

struct upoint { unsigned int x; unsigned int y; };

void transpose2 (struct upoint *p)
/* --BEGIN-- */
/*@ requires take P = RW<struct upoint>(p);
    ensures take P_post = RW<struct upoint>(p);
            P_post.x == P.y;
            P_post.y == P.x;
@*/
/* --END-- */
{
  swap(&p->x, &p->y);
}
