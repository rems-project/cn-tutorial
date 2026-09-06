// A loop with a simple post-condition

int loop_5()
/*@ ensures return == 7; @*/
{
  int ret = 0;
  int i = 0;
  while (i < 7)
  /*@ inv ret == i;
          i <= 7; @*/
  {
    i = i + 1;
    ret = i;
  }; // The exit condition implies the post-condition 
  return ret;
}
