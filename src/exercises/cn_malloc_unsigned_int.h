unsigned int *malloc__unsigned_int()
/*@ ensures take R = W<unsigned int>(return); @*/
{
  return cn_malloc(sizeof(unsigned int));
}

void free__unsigned_int (unsigned int *p)
/*@ requires take P = W<unsigned int>(p); @*/
{
  cn_free_sized(p, sizeof(unsigned int));
}
