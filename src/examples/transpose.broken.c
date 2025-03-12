struct point { int x; int y; };

void transpose (struct point *p) 
/*@ requires take P = RW<struct point>(p);
    ensures take P_post = RW<struct point>(p);
            P_post.x == P.y;
            P_post.y == P.x;
@*/
{
  int temp_x = p->x;
  int temp_y = p->y;
  /*@ assert(false); @*/
  p->x = temp_y;
  p->y = temp_x;
}
