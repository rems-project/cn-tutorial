void zero (unsigned *p)
/* --BEGIN-- */
/*@ requires take P = Block<unsigned>(p);
    ensures take P_post = Owned<unsigned>(p);
            P_post == 0u32;
@*/
/* --END-- */
{
  *p = 0;
}
