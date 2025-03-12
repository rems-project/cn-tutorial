void incr (unsigned int *p)
/*@ requires take n1 = RW<unsigned int>(p);
    ensures take n2 = RW<unsigned int>(p);
            n2 == n1 + 1u32;
@*/
{
  unsigned int n = *p;
  unsigned int m = n+1;
  *p = m;
}
