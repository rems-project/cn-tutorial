// Bad spec.
// The problem here is that the function does not dealloacte the pointer,
// but the `ensure` clause doesn't return the ownership it took, so
// the memory has "leaked".

void f(int *p)
/*@
requires
  take unussed_1 = Block(p);
ensures
  true;
@*/
{
  *p = 2;
}