unsigned int between (unsigned int p, unsigned int q)
/* --BEGIN-- */
  /*@
    requires p <= q;
    ensures return >= p;
            return <= q;
  @*/
/* --END-- */
{
  return q;
}
