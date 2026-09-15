int add(int x, int y)
/* --BEGIN-- */
/*@ requires let Sum = x + y;
             -2147483648 <= Sum; Sum <= 2147483647;
    ensures return == Sum;
@*/
/* --END-- */
{
  return x+y;
}
