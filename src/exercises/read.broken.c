unsigned int read (unsigned int *p)
/*@ requires take v1 = Owned<unsigned int>(p); @*/
{
  return *p;
}
