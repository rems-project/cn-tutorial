void swap (unsigned int *p, unsigned int *q)
/*@ requires take P = Owned<unsigned int>(p);
             take Q = Owned<unsigned int>(q);
    ensures  take P_post = Owned<unsigned int>(p);
             take Q_post = Owned<unsigned int>(q);
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
/*@ requires take P = Owned<struct upoint>(p);
    ensures take P_post = Owned<struct upoint>(p);
            P_post.x == P.y;
            P_post.y == P.x;
@*/
/* --END-- */
{
  swap(&p->x, &p->y);
}
