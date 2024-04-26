// Compute the maximum of two values, a and b. The proof shows that the code is
// equivalent to the same algorithm implemented in the spec language 

/*@
function (i32) max_spec (i32 a, i32 b)
{
  if (a > b){
    a
  } else {
    b
  }
}
@*/

int max(int a, int b)
/*@ ensures 
      (a >= b && return == a) || (a < b && return == b) @*/
/*@ ensures 
      return == max_spec(a,b) @*/
{
  if (a > b)
  {
    return a;
  }
  else
  {
    return b;
  }
}

void max_test()
{
  int v;
  v = max(-2, 7);
  assert(v == 7);
}

