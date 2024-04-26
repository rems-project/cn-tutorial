// A loop with a post-condition and a very big arbitrary constant

int loop_6(int n)
/*@ ensures return == 789398323i32 @*/ // <-- arbitrary value 
{
  int i = 0;
  while (i < 789398323)
  /*@ inv 0i32 <= i; 
          i <= 789398323i32 @*/
  {
    i = i + 1;
  };
  return i;
}
