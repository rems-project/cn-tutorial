void zero (int *p)
/* --BEGIN-- */
/*@ requires take P = Block<int>(p);
    ensures take P_post = Owned<int>(p);
            P_post == 0i32;
@*/
/* --END-- */
{
  *p = 0;
}
