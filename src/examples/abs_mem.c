int abs_mem (int *p)
/* --BEGIN-- */
/*@ requires take x = Owned<int>(p);
             -2147483648i32 < x;
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
