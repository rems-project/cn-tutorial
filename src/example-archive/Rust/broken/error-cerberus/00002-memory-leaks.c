// Tags: main, malloc, pointers, stdio
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

#include <stdio.h>
#include <stdlib.h>

int main() {
    int *my_data = malloc(sizeof(int)); // Allocate memory for an integer on the heap
    if (my_data == NULL) {
        fprintf(stderr, "Memory allocation failed\n");
        exit(EXIT_FAILURE);
    }

    *my_data = 42; // Assign the value 42 to the allocated memory
    printf("Using my_data: %d\n", *my_data);

    free(my_data); // Free the allocated memory
    my_data = NULL; // Avoid dangling pointer by setting to NULL

    return 0;
}
