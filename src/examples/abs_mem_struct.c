int abs_mem (int *p)
/* --BEGIN-- */
/*@ requires take x = Owned<int>(p);
             MINi32() < x;
    ensures take x2 = Owned<int>(p);
            x == x2;
            return == ((x >= 0i32) ? x : (0i32-x));
@*/
/* --END-- */
{
  int x = *p;
  if (x >= 0) {
    return x;
  }
  else {
    return -x;
  }
}
struct tuple {
  int x;
  int y;
};
int abs_y (struct tuple *p)
/*@ requires take s = Owned(p);
             MINi32() < s.y;
    ensures  take s2 = Owned(p);
             s == s2;
             return == ((s.y >= 0i32) ? s.y : (0i32-s.y));
@*/
{
  return abs_mem(&p->y);
}
int main()
{
    struct tuple t = { .x = 0 };
    t.y = 0x7fffffff;
    int x = abs_y(&t);
    /*@ assert (x == MAXi32() && t == { y : MAXi32(), ..t}); @*/
    t.y = (-0x7fffffff - 1)+1;
    int y = abs_y(&t);
    /*@ assert (y == MAXi32() && t == { y : MINi32() + 1i32, ..t}); @*/
    t.y = 0;
    int z = abs_y(&t);
    /*@ assert (z == 0i32 && t == { y : 0i32, ..t}); @*/
    // int bad = abs_y(0);
}
