int abs (int x)
/* --BEGIN-- */
/*@ requires -2147483648i32 < x;
    ensures return == ((x >= 0i32) ? x : (0i32-x));
@*/
/* --END-- */
{
  if (x >= 0) {
    return x;
  }
  else {
    return -x;
  }
}
