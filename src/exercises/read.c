unsigned int read (unsigned int *p)
/* --BEGIN-- */
/*@ requires take P = RW<unsigned int>(p);
    ensures take P_post = RW<unsigned int>(p);
@*/
/* --END-- */
{
  return *p;
}
