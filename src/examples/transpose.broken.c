struct point { int x; int y; };

void transpose (struct point *p) 
/*@ requires take s = Owned<struct point>(p); 
    ensures take s2 = Owned<struct point>(p); 
            s2.x == s.y;
            s2.y == s.x; 
@*/
{
  int temp_x = p->x;
  int temp_y = p->y;
  /*@ assert(false); @*/
  p->x = temp_y;
  p->y = temp_x;
}
