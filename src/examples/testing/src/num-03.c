
// Find a needle in a heystack.
// We don't use the source code to guide test generation.
//
// Because of this, we are unlikely to find the mismatch
// between the spec and the implementation.

int f(int x)
/*@
  requires
    true;
  ensures
    return == x;
@*/
{
  return x + (x == 12345567 ? 1 : 0);
}