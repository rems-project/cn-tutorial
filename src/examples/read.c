int read (int *p)
/* --BEGIN-- */
/*@ requires take P = Owned<int>(p);
    ensures take P_post = Owned<int>(p);
@*/
/* --END-- */
{
  return *p;
}
