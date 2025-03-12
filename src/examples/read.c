int read (int *p)
/* --BEGIN-- */
/*@ requires take P = RW<int>(p);
    ensures take P_post = RW<int>(p);
@*/
/* --END-- */
{
  return *p;
}
