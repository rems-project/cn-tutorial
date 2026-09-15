void incr (unsigned int *p)
/*@ requires take P = RW<unsigned int>(p);
             P < MAXu32();
    ensures take P_post = RW<unsigned int>(p);
            P_post == P + 1;
@*/
{
  unsigned int n = *p;
  unsigned int m = n+1;
  *p = m;
}
