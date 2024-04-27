int read (int *p)
/* --BEGIN-- */
/*@ requires take v1 = Owned<int>(p);
    ensures take v2 = Owned<int>(p);
@*/
/* --END-- */
{
  return *p;
}
