unsigned int double (unsigned int *p)
/* --BEGIN-- */
/*@ requires take P = RW<unsigned int>(p);
    ensures  take P_post = RW<unsigned int>(p);
             return == P + P;
             P_post == P;
@*/
/* --END-- */
{
  int n = *p;
  int m = n + n;
  return m;
}
