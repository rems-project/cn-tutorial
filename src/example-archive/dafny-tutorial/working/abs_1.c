// Compute the absolute value a function.

/*@
function (integer) abs_spec(integer x)
{
  if (x < 0) {
    (0 - x)
  } else {
    x
  }
}
@*/

int abs(int x)
/*@ requires 
      let MINi32 = -2147483647;
      MINi32 < x;
    ensures 
      0 <= return; 
      (x < 0 && return == (0 - x)) || (0 <= x && return == x); 
      0 <= return && (return == x || return == (0 - x));  // Same property
      return == abs_spec(x); @*/                          // Same property
{
  if (x < 0)
  {
    return (-1 * x);
  }
  else
  {
    return x;
  }
}

void abs_testing()
{
  int v = abs(3);
  assert(0 <= v);
  assert(v == 3);
}
