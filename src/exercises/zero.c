void zero (unsigned int *p)
/* --BEGIN-- */
/*@ requires take P = W<unsigned int>(p);
    ensures take P_post = RW<unsigned int>(p);
            P_post == 0u32;
@*/
/* --END-- */
{
  *p = 0;
}
