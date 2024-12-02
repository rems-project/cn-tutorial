// Bad spec.
// Allocations are OK, but value in memory is wrong.

void f(int *p)
/*@
requires
  take unussed_1 = Block(p);
ensures
  take x = Owned(p);
  x == 3i32;
@*/
{
  *p = 2;
}