unsigned int double_it (unsigned int *p)
/* --BEGIN-- */
/*@ requires take P = RW<unsigned int>(p);
    ensures  take P_post = RW<unsigned int>(p);
             return == P + P;
             P_post == P;
@*/
/* --END-- */
{
  unsigned int n = *p;
  unsigned int m = n + n;
  return m;
}
