// Cast a pointer to an int, and back. This variant requires some flow-sensitive
// reasoning to prove that the original pointer is validly restored 

#include <stdint.h> // For uintptr_t, intptr_t

int cast_2()
/*@ ensures return == 7i32; @*/
{
  int x = 7;
  int *ptr_original = &x;

  // Cast pointer to uintptr_t
  uintptr_t ptr_as_int = (uintptr_t) ptr_original;

  // Copy the pointer and mess around with it 
  uintptr_t ptr_as_int_copy = ptr_as_int;
  ptr_as_int_copy = ptr_as_int_copy + 1;
  if (ptr_as_int < ptr_as_int_copy) // Check for overflow 
  {
    ptr_as_int_copy = ptr_as_int_copy - 1;
    int *ptr_restored = (int *)ptr_as_int_copy;

    int ret = *ptr_restored;

    return ret;
  } else {
    return 7; 
  }
}
