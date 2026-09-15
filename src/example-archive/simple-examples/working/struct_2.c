// Assign directly into a struct field using pointer arithmetic

#include <stddef.h> // For offsetof macro

struct s
{
  int x;
  int y;
};

int struct_2()
/*@ ensures return == 7; @*/
{
  struct s target;

  // Assign to x and y in the normal way
  target.x = 69; 
  target.y = 42;

  // Directly assign to y via pointer arithmetic
  int *fieldPtr = (int *)((char *)&target + offsetof(struct s, y));
  *fieldPtr = 7;
  target.x = 8;

  // Read from field y via pointer arithmetic 
  int ret = *fieldPtr;
  #ifdef CN_INSTRUMENT
  /*@ assert(target.x == 8); @*/
  #else
  assert(target.x == 8);
  #endif
  return ret;
}

int main(void)
/*@ trusted; @*/
{
  struct_2();
}