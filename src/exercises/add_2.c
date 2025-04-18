int add(int x, int y)
/* --BEGIN-- */
/*@ requires let Sum = (i64) x + (i64) y;
             (i64)MINi32() <= Sum; Sum <= (i64)MAXi32();
    ensures return == (i32) Sum;
@*/
/* --END-- */
{
  return x+y;
}
