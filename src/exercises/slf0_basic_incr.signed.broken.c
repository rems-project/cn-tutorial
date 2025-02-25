void incr (int *p)
/*@ requires take P = Block<int>(p); 
    ensures take P_post = Owned<int>(p); 
@*/
{
  *p = *p+1;
}
