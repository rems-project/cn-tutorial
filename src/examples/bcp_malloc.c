void malloc_unsigned (unsigned int *p)
/*@ trusted
    ensures take n = Block<unsigned int>(p)
@*/
{
}

void free_unsigned (unsigned int *p)
/*@ trusted
    requires take n = Block<unsigned int>(p)
@*/
{
}

unsigned int id (unsigned int i, unsigned int *p)
/*@ requires take n1 = Block<unsigned int>(p)
    ensures take n2 = Owned<unsigned int>(p);
            n2 == i;
            return == i
@*/
{
  *p = i;
  unsigned int j = *p;
  return j;
}


void add_easy (unsigned int i, unsigned int *p)
/*@ requires take n1 = Block<unsigned int>(p);
             let ret = (i64)i + 1i64;
             ret <= 2147483647i64
    ensures take n2 = Owned<unsigned int>(p);
            n2 == (u32)ret
@*/
{
  *p = i;
  *p = *p + 1;
  unsigned int j = *p;
}


unsigned int add (unsigned int i)
/*@ requires let j = (i64)i + 1i64;
             j <= 2147483647i64
    ensures return == (u32)j
@*/
{
  unsigned int *p;
  malloc_unsigned(p);
  *p = i;
  *p = *p + 1;
  unsigned int j = *p;
  free_unsigned(p);
  return j;
}
