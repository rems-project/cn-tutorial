int quadruple_mem (int *p)
/* --BEGIN-- */
/*@ requires take P = RW<int>(p);
             let P64 = (i64) P;
             (i64)MINi32() <= P64 * 4i64; P64 * 4i64 <= (i64)MAXi32();
    ensures take P_post = RW<int>(p);
            P_post == P;
            return == 4i32 * P;
 @*/
/* --END-- */
{
  int m = *p + *p;
  return m + m;
}
