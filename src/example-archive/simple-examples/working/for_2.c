// A trivial for-loop with an invariant 
// TODO: doesn't parse 

int for_1() 
{
  int acc = 0; 
  for(int i = 0; i <= 99; i++)
  /*@ inv acc < 99 @*/
  {
    acc = i; 
  }; 
  return acc;
}
