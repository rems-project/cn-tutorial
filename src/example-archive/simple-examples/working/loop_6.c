// A loop with a post-condition and a very big arbitrary constant

int loop_6(int n)
/*@ ensures return == 789398323; @*/ // <-- arbitrary value 
{
  int i = 0;
  while (i < 789398323)
  /*@ inv 0 <= i; 
          i <= 789398323; @*/
  {
    i = i + 1;
  };
  return i;
}
