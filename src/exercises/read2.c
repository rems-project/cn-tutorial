int read (int *p)
/*@ requires take P = Owned<int>(p);
    ensures take P_post = Owned<int>(p);
            return == P;
            P_post == P;
@*/
{
  return *p;
}
