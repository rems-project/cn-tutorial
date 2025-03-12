void zero (int *coord) 
/*@ requires take Coord = W<int>(coord);
    ensures take Coord_post = RW<int>(coord);
            Coord_post == 0i32; @*/
{
  *coord = 0;
}

struct point { int x; int y; };

void init_point(struct point *p) 
/*@ requires take P = W<struct point>(p);
    ensures take P_post = RW<struct point>(p);
            P_post.x == 0i32;
            P_post.y == 0i32;
@*/
{
  zero(&p->x);
  zero(&p->y);
}
