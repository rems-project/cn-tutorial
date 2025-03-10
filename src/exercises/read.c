unsigned int read (unsigned int *p)
/* --BEGIN-- */
/*@ requires take P = Owned<unsigned int>(p);
    ensures take P_post = Owned<unsigned int>(p);
@*/
/* --END-- */
{
  return *p;
}
