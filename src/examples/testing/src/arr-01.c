// Tests should pass: we just assert that we have a valid chunk of memory.

void preserve(int size, int *p)
/*@
requires
  take a1 = each(i32 i; 0i32 <= i && i < size) { Owned<int>(array_shift<int>(p,i)) };
ensures
  take a2 = each(i32 i; 0i32 <= i && i < size) { Owned<int>(array_shift<int>(p,i)) };
@*/
{
}
