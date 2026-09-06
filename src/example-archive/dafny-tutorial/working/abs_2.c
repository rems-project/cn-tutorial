// A specialized version of abs. The precondition requires that the input value x
// is negative

int abs_2(int x)
/*@ requires 
      let MINi32 = -2147483647;

      MINi32 <= x; 
      x < 0;
    ensures 
      0 <= return; 
      (return == x || return == (0 - x)); @*/
{
  return -x;
}

