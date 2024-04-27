void zero (int *p) 
/*@ requires take u = Block<int>(p);
    ensures take v = Owned<int>(p);
            v == 0i32; @*/
{
  *p = 0;
}

struct point { int x; int y; };

void init_point(struct point *p) 
/*@ requires take s = Block<struct point>(p);
    ensures take s2 = Owned<struct point>(p);
            s2.x == 0i32;
            s2.y == 0i32;
@*/
{
  zero(&p->x);
  zero(&p->y);
}
