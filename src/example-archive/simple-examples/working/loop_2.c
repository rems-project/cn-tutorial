// A trivial loop that never terminates. CN uses a partial-correctness logic so
// if the loop never exits, we can prove whatever post-condition we want,
// including false

int loop_2()
/*@ ensures return == 42i32 @*/  // <-- Oops, prove whatever we want 
{
  int i = 0;
  while (i < 10)
  /*@ inv i == 0i32 @*/  // <-- Loop exit condition never satisfied
  {
    // Don't do anything
  };
  return 7; 
}
