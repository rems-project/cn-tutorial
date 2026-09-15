int add(int x, int y)
/* --BEGIN-- */
/*@ requires let Sum = x + y;
             MINi32() <= Sum; Sum <= MAXi32();
    ensures return == Sum;
@*/
/* --END-- */
{
  return x+y;
}
