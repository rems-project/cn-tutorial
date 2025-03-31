void zero (unsigned int *coord) 
/*@ requires take Coord = RW<unsigned int>(coord);
    ensures take Coord_post = RW<unsigned int>(coord);
            Coord_post == 0u32; @*/
{
  *coord = 0;
}

struct point { unsigned int x; unsigned int y; };

void init_point(struct point *p) 
/*@ requires take P = RW<struct point>(p);
    ensures take P_post = RW<struct point>(p);
            P_post.x == 0u32;
            P_post.y == 0u32;
@*/
{
  zero(&p->x);
  zero(&p->y);
}
