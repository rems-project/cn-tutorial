// Prove that an assertion cannot fail 

#include <assert.h>

int assert_1(int x)
/*@ requires x == 7;
    ensures return == 0; @*/
{
  x = 0;
  assert(x == 0);
  return (x);
}

// An alternative syntax for the same assertion: 

int assert_1_alt(int x)
/*@ requires x == 7;
    ensures return == 0; @*/
{
  x = 0;
  /*@ assert(x == 0); @*/
  return (x);
}
