int abs (int x)
/* --BEGIN-- */
/*@ requires MINi32() < x;
    ensures return == ((x >= 0) ? x : (0-x));
@*/
/* --END-- */
{
  if (x >= 0) {
    return x;
  } else {
    return -x;
  }
}
