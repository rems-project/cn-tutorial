int add(int x, int y)
/* --BEGIN-- */
/*@ requires let Sum = x + y;
             -2147483648 <= Sum; Sum <= 2147483647; @*/
/* --END-- */
{
  return x+y;
}
