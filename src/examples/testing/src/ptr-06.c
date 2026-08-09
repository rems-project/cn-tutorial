// Swap the contents of two pointers, allowing for aliasing.

/*@
type_synonym SwapState = { boolean same, i32 p, i32 q }

predicate SwapState SwapPre(pointer p, pointer q) {
  if (ptr_eq(p,q)) {
    return { same: true, p: 0i32, q: 0i32 };
  } else {
    // Not aliased, both pointers initialized.
    take x = Owned<int>(p);
    take y = Owned<int>(q);
    return { same: false, p: x, q: y };
  }
}

predicate (boolean) SwapPost(pointer p, pointer q, SwapState pre) {
  if (pre.same) {
    return true;
  } else {
    take x = Owned<int>(p);
    take y = Owned<int>(q);
    assert(x == pre.q);
    assert(y == pre.p);
    return true;
  }
}
@*/

void swap(int *p, int *q)
/*@
requires
  take pre = SwapPre(p,q);
ensures
   take unused = SwapPost(p,q,pre);
@*/
{
  if (p == q) return;
  int x = *p;
  *p = *q;
  *q = x;
}

void swap_same()
{
  int x;
  swap(&x,&x);  // Aliasing OK
  swap(0,0);    // We don't touch the pointers when they are the same.
  // swap(0,&x)  will cause an error
}