unsigned read (unsigned *p)
/*@ requires take v1 = Owned<unsigned>(p); @*/
{
  return *p;
}
