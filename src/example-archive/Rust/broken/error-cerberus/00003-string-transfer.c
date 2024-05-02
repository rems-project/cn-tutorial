// Tags: main, malloc, pointers, stdio
/** Description:

    This example demonstrates how Rust transfers ownership of pointers
    and prevents dangling pointers among other safety guarantees. By
    enforcing strict ownership rules at compile time, Rust ensures
    that memory is managed safely, eliminating common errors such as
    use-after-free or accessing uninitialized memory.
*/

/* Rust code:
   
fn create_string() -> String {
    let s = String::from("Hello, Rust!");
    s  // Ownership of 's' is transferred to the caller
}

fn use_string(s: &String) {
    println!("Using string: {}", s);
}

fn main() {
    let my_string = create_string(); // 'my_string' takes ownership of the String returned by 'create_string'
    use_string(&my_string);  // A reference is passed, so 'my_string' retains ownership
    
    // The following are safe to use
    println!("Still can use my_string: {}", my_string);
    use_string(&my_string);  // Demonstrates that 'my_string' is still valid and not dangling
}
*/

/* C + CN translation */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Function to create a string
char* create_string() {
    char *s = malloc(20 * sizeof(char));  // Allocate memory for the string
    if (s == NULL) {
        fprintf(stderr, "Memory allocation failed\n");
        exit(EXIT_FAILURE);
    }
    strcpy(s, "Hello, C!");  // Initialize the string
    return s;  // Return the pointer (ownership transfer to the caller)
}

// Function to use the string
void use_string(const char *s) {
    printf("Using string: %s\n", s);
}

int main() {
    char *my_string = create_string(); // Takes ownership of the memory returned by create_string
    use_string(my_string);  // Pass the pointer to use_string

    // Can still use my_string
    printf("Still can use my_string: %s\n", my_string);

    free(my_string);  // Explicitly free the memory allocated in create_string
    my_string = NULL;  // Avoid dangling pointer by setting it to NULL after freeing

    return 0;
}
