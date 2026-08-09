// Swap the values in 2 pointers.
// Note that the `Owned` precicates implicitly assert that there
// is no aliasing between `p` and `q`.


void swap(int *p, int *q)
/*@
requires
  take p1 = Owned(p);
  take q1 = Owned(q);
ensures
  take p2 = Owned(p);
  take q2 = Owned(q);
  p1 == q2;
  q1 == p2;
@*/
{
  int x = *p;
  *p = *q;
  *q = x;
}

// This should fail, because of the aliasing.
void swap_same()
{
  int x;
  swap(&x,&x);
}