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

struct point { unsigned int x; unsigned int y; };

void transpose2 (struct point *p)
/* --BEGIN-- */
/*@ requires take P = RW<struct point>(p);
    ensures take P_post = RW<struct point>(p);
            P_post.x == P.y;
            P_post.y == P.x;
@*/
/* --END-- */
{
  swap(&p->x, &p->y);
}
