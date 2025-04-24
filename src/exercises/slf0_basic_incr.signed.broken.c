void incr (int *p)
/*@ requires take P = W<int>(p); 
    ensures take P_post = RW<int>(p); 
@*/
{
  *p = *p+1;
}
