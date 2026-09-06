// A conditional return value, and ternary conditional operator in CN 

int cond_1 (int i) 
/*@ ensures 
      return == (i == 0 ? 0 : 1); @*/
{
  if (i == 0) {
    return 0; 
  } else {
    return 1; 
  }
}
