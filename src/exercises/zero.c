void zero (unsigned int *p)
/* --BEGIN-- */
/*@ requires take P = Block<unsigned int>(p);
    ensures take P_post = Owned<unsigned int>(p);
            P_post == 0u32;
@*/
/* --END-- */
{
  *p = 0;
}
