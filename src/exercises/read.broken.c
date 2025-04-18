unsigned int read (unsigned int *p)
/*@ requires take P = RW<unsigned int>(p); @*/
{
  return *p;
}
