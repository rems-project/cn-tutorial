// Bad spec.
// The problem here is that the function does not dealloacte the pointer,
// but the `ensure` clause does return the ownership it took.

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