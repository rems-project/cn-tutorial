void incr (unsigned int *p)
--BEGIN--
/*@ requires take n1 = Owned<unsigned int>(p)
    ensures take n2 = Owned<unsigned int>(p);
            n2 == n1 + 1u32
@*/
--END--
{
  unsigned int n = *p;
  unsigned int m = n+1;
  *p = m;
}
