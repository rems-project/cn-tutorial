void zero (int *p)
/* --BEGIN-- */
/*@ requires take P = W<int>(p);
    ensures take P_post = RW<int>(p);
            P_post == 0i32;
@*/
/* --END-- */
{
  *p = 0;
}
