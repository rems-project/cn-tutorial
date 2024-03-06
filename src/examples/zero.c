void zero (int *p) 
--BEGIN--
/*@ requires take u = Block<int>(p)
    ensures take v = Owned<int>(p);
            v == 0i32 @*/
--END--
{
  *p = 0;
}
