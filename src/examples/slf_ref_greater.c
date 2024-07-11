// TODO - REVISIT

// #include "malloc.h"

unsigned int *mallocUnsignedInt ()
/*@ requires true;
    ensures take v = Block<unsigned int>(return);
@*/
{
   return 0; 
}


unsigned int *ref_greater_abstract (unsigned int *p)
/* --BEGIN-- */
/*@ requires take m1 = Owned<unsigned int>(p);
             m1 < 4294967295u32;
    ensures take m2 = Owned<unsigned int>(p);
            take n2 = Owned<unsigned int>(return);
            m1 == m2;
            m1 <= n2;
@*/
/* --END-- */
{
  unsigned int* q = mallocUnsignedInt();
  *q = *p + 1;
  return q;
}

int main()
{
    unsigned int x = 5;
    unsigned int *q = ref_greater_abstract(&x);
    /*@ assert(!ptr_eq(&x, q)); @*/
    /*@ assert(*q == x + 1u32); @*/
}
