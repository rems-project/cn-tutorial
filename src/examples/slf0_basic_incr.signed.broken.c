void incr (int *p)
--BEGIN--
/*@ requires take u = Block<int>(p)
    ensures take v = Owned<int>(p) 
@*/
--END--
{
  *p = *p+1;
}
