int abs (int x)
/* --BEGIN-- */
/*@ requires MINi32() < x;
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
int main()
/*@ trusted; @*/
{
    int x = abs(0x7fffffff);
    /*@ assert (x == MAXi32()); @*/
    int y = abs((-0x7fffffff - 1)+1);
    /*@ assert (y == MAXi32()); @*/
    int z = abs(0);
    /*@ assert (z == 0i32); @*/
}
