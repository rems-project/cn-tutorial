int add(int x, int y)
/* --BEGIN-- */
/*@ requires let sum = (i64) x + (i64) y;
             -2147483648i64 <= sum; sum <= 2147483647i64
    ensures return == (i32) sum
@*/
/* --END-- */
{
  return x+y;
}
