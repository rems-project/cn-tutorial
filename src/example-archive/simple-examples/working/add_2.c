// Add two numbers together. This function is trivially non-faulting because the
// requires-clause sets one integer to be zero 

signed int add_2(signed int x, signed int y)
/*@ requires x == 0i32; @*/
/*@ ensures return == y; @*/
{
  signed int i;
  i = x + y;
  return i;
}
