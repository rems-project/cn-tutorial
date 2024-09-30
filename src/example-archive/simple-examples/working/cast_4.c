// Cast a pointer to an int, and back. This variant passes memory from the
// context

#include <stdint.h> // For uintptr_t, intptr_t
#define OFFSET 374328

int cast_4(int *ptr_original)
/*@ requires take Pre = Block<int>(ptr_original); @*/
/*@ ensures take Post = Owned<int>(ptr_original);
            return == 7i32; @*/
{
  *ptr_original = 7;
  // Cast pointer to uintptr_t
  uintptr_t ptr_as_int = (uintptr_t) ptr_original;

  // Copy the pointer and mess around with it 
  uintptr_t ptr_as_int_copy = ptr_as_int;
  ptr_as_int_copy = ptr_as_int_copy + OFFSET;
  if (ptr_as_int < ptr_as_int_copy) // Check for overflow 
  {
    ptr_as_int_copy = ptr_as_int_copy - OFFSET;
    int *ptr_restored = __cerbvar_copy_alloc_id(ptr_as_int_copy, ptr_original);

    int ret = *ptr_restored;

    return ret;
  } else {
    return 7; 
  }
}
