// Testing will succeed even though verification will not.
// In this case the specificaiton for `f` is too weak:
// after calling `f` we know only that `p` is allocated, not that
// it is initialized or what is its value.

void f(int *p)
/*@
  requires
    take unused = Block(p);
  ensures
    take x = Block(p);
@*/
{
  *p = 2;
}

void g() {
  int x;
  f(&x);
  /*@ assert(x == 2i32); @*/
  // Succeeds despite weak spec, because check is done at runtime.
}