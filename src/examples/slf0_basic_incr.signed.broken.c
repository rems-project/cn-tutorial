void incr (int *p)
/*@ requires take u = Block<int>(p)
    ensures take v = Owned<int>(p) 
@*/
{
  *p = *p+1;
}
