int read (int *p)
/*@ requires take P = RW<int>(p);
    ensures take P_post = RW<int>(p);
            return == P;
            P_post == P;
@*/
{
  return *p;
}
