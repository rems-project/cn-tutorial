// Spec and implementation match.
void f(int *p, int x)
/*@
requires
  take unussed_1 = Block(p);
ensures
  take v = Owned(p);
  v == x;
@*/
{
  *p = x;
}