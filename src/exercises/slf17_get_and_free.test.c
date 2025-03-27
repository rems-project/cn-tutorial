#include "cn_malloc.h"
#include "cn_malloc_unsigned_int.h"

/* ------------- */

unsigned int get_and_free (unsigned int *p)
/*@ requires take P = RW(p);
    ensures return == P;
@*/
{
  unsigned int v = *p;
  free__unsigned_int (p);
  return v;
}

unsigned int *malloc_and_set (unsigned int x)
/*@ ensures take P = RW(return);
            P == x;
@*/
{
  unsigned int *p = malloc__unsigned_int ();
  *p = x;
  return p;
}

/* BCP: Why doesn't this compile? */
// unsigned int tester() {
// /*@ requires true;
//     ensures return = 42;
// @*/
//   unsigned int *p = malloc_and_set (42);
//   unsigned int v = get_and_free (p);
//   return v;
// }
