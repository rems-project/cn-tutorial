int quadruple_mem (int *p)
/* --BEGIN-- */
/*@ requires take P = RW<int>(p);
             MINi32() <= P * 4; P * 4 <= MAXi32();
    ensures take P_post = RW<int>(p);
            P_post == P;
            return == 4 * P;
 @*/
/* --END-- */
{
  int m = *p + *p;
  return m + m;
}
