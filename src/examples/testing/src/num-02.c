
// Find a needle in a heystack
// We do use the `requires` spec to guide test generation.
//
// Note that had we not used the `requires` clause, random inputs
// would lead to a result violating the `ensures` clause.

int f(int x)
/*@
  requires
    x == 12345678i32;
  ensures
    return == 12345679i32;
@*/
{
  return x + 1;
}