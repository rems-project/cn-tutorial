int abs_mem (int *p)
/* --BEGIN-- */
/*@ requires take x = Owned<int>(p);
             MINi32() < x;
    ensures take x_post = Owned<int>(p);
            x == x_post;
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
