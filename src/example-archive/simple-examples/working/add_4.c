// Increment an input by 1

signed int inc_1(signed int i)
/*@ requires 
      let MAXi32 = 2147483647; 
      i + 1 <  MAXi32;
    ensures return == i + 1; @*/
{
  i = i + 1;
  return i;
}
