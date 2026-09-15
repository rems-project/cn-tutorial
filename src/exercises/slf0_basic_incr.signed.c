void incr (int *p)
/*@ requires take P = RW<int>(p);
             P + 1 <= MAXi32();
    ensures take P_post = RW<int>(p);
            P_post == P + 1;
@*/
{
  *p = *p+1;
}
