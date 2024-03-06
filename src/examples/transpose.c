struct point { int x; int y; };

void transpose (struct point *p) 
/*@ requires take s = Owned<struct point>(p)
    ensures take s2 = Owned<struct point>(p);
            s2.x == s.y;
            s2.y == s.x
@*/
{
  struct point s = *p;
  p->x = s.y;
  p->y = s.x;
}
