unsigned read (unsigned *p)
/* --BEGIN-- */
/*@ requires take P = Owned<unsigned>(p);
    ensures take P_post = Owned<unsigned>(p);
@*/
/* --END-- */
{
  return *p;
}
