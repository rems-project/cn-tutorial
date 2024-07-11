#include <limits.h>

unsigned int example_let (unsigned int n) 
/*@ ensures return == 2u32 * n;
@*/
{
  unsigned int a = n+1;
  unsigned int b = n-1;
  return a+b;
}

int main()
/*@ trusted; @*/
{
    unsigned int x = example_let(5);
    /*@ assert(x == 10u32); @*/

    // uncomment for intentional fail

    // x = example_let(0);
    // /*@ assert (x == MAXu32()); @*/

    // x = example_let(UINT_MAX);
    // /*@ assert (x == MAXu32() - 1u32); @*/
}
