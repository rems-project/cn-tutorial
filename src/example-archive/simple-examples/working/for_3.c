// A trivial for-loop 
// TODO: doesn't parse 

int for_3() 
{
  int acc = 0; 
  for(int i = 0; i < 10; i++) 
  /*@ inv 0 <= i; 
          i <= 10;
          acc <= 10; @*/
  {
    acc = i; 
  }; 
  return acc;
}
