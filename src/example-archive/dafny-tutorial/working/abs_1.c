// Compute the absolute value a function.

/*@
function (i32) abs_spec(i32 x)
{
  if (x < 0i32) {
    (0i32 - x)
  } else {
    x
  }
}
@*/

int abs(int x)
/*@ requires 
      let MINi32 = (i64) -2147483647i64;
      MINi32 < (i64) x;
    ensures 
      0i32 <= return; 
      (x < 0i32 && return == (0i32 - x)) || (0i32 <= x && return == x); 
      0i32 <= return && (return == x || return == (0i32 - x));  // Same property
      return == abs_spec(x); @*/                                // Same property
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
