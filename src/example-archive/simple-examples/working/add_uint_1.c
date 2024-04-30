// Add two unsigned ints together. Note we don't need to add a lower bound any
// more because the inputs are guaranteed positive

unsigned int add_uint_1(unsigned int x, unsigned int y)
/*@ requires 
      let MAXi32 = 2147483647i64;
      (i64) x + (i64) y <= MAXi32; @*/
/*@ ensures return == x + y; @*/
{
  signed int i;
  i = x + y;
  return i;
}
