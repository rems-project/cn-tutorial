int read (int *p)
/*@ requires take v1 = Owned<int>(p) @*/
{
  return *p;
}
