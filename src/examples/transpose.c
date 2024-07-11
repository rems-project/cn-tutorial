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
  p->x = temp_y;
  p->y = temp_x;
}

int main()
/*@ trusted; @*/
{
    struct point p = {.x = 3, .y = 4};
    transpose(&p);
    /*@ assert (p.x == 4i32); @*/
    /*@ assert (p.y == 3i32); @*/
}
