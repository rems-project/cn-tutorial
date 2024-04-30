// Add two numbers together. This can overflow, but we can add a requires-clause
// that enforces that x and y are both zero. This makes the function trivially
// non-faulting.

signed int add_1(signed int x, signed int y)
/*@ requires x == 0i32; y == 0i32; @*/
/*@ ensures return == x + y; @*/
{
  signed int i;
  i = x + y;
  return i;
}
