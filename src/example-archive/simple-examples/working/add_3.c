// Add two numbers together. Verifying the addition function for arbitrary
// inputs requires that the total cannot overflow.

signed int add_3(signed int x, signed int y)
/*@ requires 
      let MAXi32 = 2147483647; 
      let MINi32 = -2147483648;
      let sum = x + y;
      MINi32 <= sum; sum <= MAXi32;
    ensures return == x + y; @*/
{
  signed int i;
  i = x + y;
  return i;
}
