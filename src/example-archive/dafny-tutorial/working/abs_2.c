// A specialized version of abs. The precondition requires that the input value x
// is negative

int abs_2(int x)
/*@ requires 
      let MINi32 = (i64) -2147483647i64;

      MINi32 <= (i64) x; 
      x < 0i32;
    ensures 
      0i32 <= return; 
      (return == x || return == (0i32 - x)); @*/
{
  return -x;
}

