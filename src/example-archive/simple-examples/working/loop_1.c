// A trivial loop that immediately exits. CN is able to determine that the
// assignment never happens. 

int loop_1()
/*@ ensures return == 7i32; @*/
{
  int i = 0;
  while (i != 7)
  {
    i = 42; // Unreachable 
  };
  return i;
}

