
// An example where the testing should catch the difference between
// the spec and the code.

int f(int x)
/*@
  requires
    true;
  ensures
    return == x;
@*/
{
  return x + 1;
}
