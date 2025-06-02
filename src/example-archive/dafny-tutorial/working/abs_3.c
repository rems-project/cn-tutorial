// A specialized version of abs. The precondition requires that the input x is
// always -1 

int abs_3(int x)
/*@ requires 
      x == (0i32 - 1i32);  // TODO: syntax is bad 
    ensures 
      0i32 <= return;
      (return == x || return == (0i32 - x)); 
      return == 1i32; @*/
{
  return x + 2;
}
