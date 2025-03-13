unsigned int read (unsigned int *p)
/*@ requires take v1 = RW<unsigned int>(p); @*/
{
  return *p;
}
