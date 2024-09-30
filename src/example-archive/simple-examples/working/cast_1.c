// Cast a pointer to an int, and back
// In regular VIP, this does not require a copy_alloc_id but as implemented
// currently in CN, it does.

#include <stdint.h> // For uintptr_t, intptr_t

int cast_1()
/*@ ensures return == 7i32; @*/
{
  int x = 7;
  int *ptr_original = &x;

  // Cast pointer to uintptr_t
  uintptr_t ptr_as_int = (uintptr_t) ptr_original;

  // Cast back to pointer
  int *ptr_restored = __cerbvar_copy_alloc_id(ptr_as_int, &x);

  // Dereference the pointer 
  int ret = *ptr_restored;

  return ret;
}
