int read (int *p)
/*@ requires take v1 = RW<int>(p); @*/
{
  return *p;
}
