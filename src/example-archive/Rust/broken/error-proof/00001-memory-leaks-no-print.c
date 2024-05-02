// Tags: main, malloc, pointers
/** Description:

    Rust's `Box` types are automatically deallocated when they go out
    of scope. The type syste, also helps to ensure that no memory is
    leaked.

    In the corresponding C program, we must manually allocate and
    deallocate the pointer. At least CN can help us verify that no
    memory is leaked.
*/

/* Rust code:
   
fn main() {
    let my_data = Box::new(42); // Dynamically allocate an integer on the heap
    println!("Using my_data: {}", my_data);
    // The integer is automatically deallocated when `my_data` goes out of scope
}

*/

/* C + CN translation */

#include <stdlib.h>

int main() {
  int ret = 0;
  int *my_data = malloc(sizeof(int)); // Allocate memory for an integer on the heap
  if (my_data == NULL) {
    exit(EXIT_FAILURE);
  }
  
  *my_data = 42; // Assign the value 42 to the allocated memory
  ret += *my_data;
  
  free(my_data); // Free the allocated memory
  my_data = NULL; // Avoid dangling pointer by setting to NULL
  
  return ret;
}
