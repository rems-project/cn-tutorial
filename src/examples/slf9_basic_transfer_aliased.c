void transfer (unsigned int *p, unsigned int *q)
/*@ requires take n1 = Owned(p);
             ptr_eq(p,q);
    ensures  take n2 = Owned(p);
             n2 == 0u32;
@*/
{
  unsigned int n = *p;
  unsigned int m = *q;
  unsigned int s = n + m;
  *p = s;
  *q = 0;
}
