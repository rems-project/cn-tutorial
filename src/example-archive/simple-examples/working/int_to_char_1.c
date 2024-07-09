// Take an integer and require that it is small enough to represent as a char.
// Then safely store the result in a char variable. Without the requires clause
// this would be UB 

void 
int_to_char_1(int a) 
/*@ requires 
      (i32) MINu8() <= (i32) a; 
      (i32) a <= (i32) MAXu8(); @*/
{
  char b; 
  b = a; 
  return; 
}