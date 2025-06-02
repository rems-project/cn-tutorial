// Increment an input by 1

signed int inc_1(signed int i)
/*@ requires 
      let MAXi32 = 2147483647i64; 
      (i64) i + 1i64 <  MAXi32;
    ensures return == i + 1i32; @*/
{
  i = i + 1;
  return i;
}
