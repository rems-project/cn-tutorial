// A specialized version of abs. The precondition requires that the input x is
// always -1 

int abs_3(int x)
/*@ requires 
      x == (0 - 1);  // TODO: syntax is bad 
    ensures 
      0 <= return;
      (return == x || return == (0 - x)); 
      return == 1; @*/
{
  return x + 2;
}
