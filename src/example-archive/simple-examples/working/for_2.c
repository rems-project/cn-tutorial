// A trivial for-loop with an invariant 

int for_2() 
{
  int acc = 0; 
  int i; 
  for(i = 0; i < 10; i++)
  /*@ inv 0i32 <= i; 
          i <= 10i32;
          acc <= 10i32 @*/
  {
    acc = i; 
  }; 
  return acc;
}
