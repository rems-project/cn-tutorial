void zero (unsigned *coord) 
/*@ requires take Coord = Block<unsigned>(coord);
    ensures take Coord_post = Owned<unsigned>(coord);
            Coord_post == 0u32; @*/
{
  *coord = 0;
}

struct point { unsigned x; unsigned y; };

void init_point(struct point *p) 
/*@ requires take P = Block<struct point>(p);
    ensures take P_post = Owned<struct point>(p);
            P_post.x == 0u32;
            P_post.y == 0u32;
@*/
{
  zero(&p->x);
  zero(&p->y);
}
