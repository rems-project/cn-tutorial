struct point { unsigned x; unsigned y; };

void transpose (struct point *p) 
/*@ requires take P = Owned<struct point>(p);
    ensures take P_post = Owned<struct point>(p);
            P_post.x == P.y;
            P_post.y == P.x;
@*/
{
  unsigned temp_x = p->x;
  unsigned temp_y = p->y;
  /*@ assert(false); @*/
  p->x = temp_y;
  p->y = temp_x;
}
