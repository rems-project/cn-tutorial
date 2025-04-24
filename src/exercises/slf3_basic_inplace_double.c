void inplace_double (unsigned int *p)
/* --BEGIN-- */
/*@ requires take P = RW<unsigned int>(p);
    ensures  take P_post = RW<unsigned int>(p);
             P_post == P + P;
@*/
/* --END-- */
{
  unsigned int n = *p;
  unsigned int m = n + n;
  *p = m;
}
