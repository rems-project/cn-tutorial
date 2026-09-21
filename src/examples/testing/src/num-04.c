
// Find a needle in a heystack.
// We don't use the `ensures` spec in test generation.
//
// Because of this, we are unlikely to find the mismatch
// between the spec and the implementation.

int f(int x)
/*@
  requires
    true;
  ensures
    let delta = if (x == 127i32) { 1i32 } else { 0i32 };
    return == x + delta;
@*/
{
  return x;
}