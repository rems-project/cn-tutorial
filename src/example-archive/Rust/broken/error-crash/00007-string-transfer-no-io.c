// Tags: main, malloc, pointers
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
#include <stdlib.h>
#include <string.h>

// Global string to hold a copy
char global_string[20];

// Function to create a string
char* create_string() {
    char *s = malloc(20 * sizeof(char));  // Allocate memory for the string
    if (s == NULL) {
        exit(EXIT_FAILURE);  // Exit if memory allocation fails
    }
    strcpy(s, "Hello, C!");  // Initialize the string
    return s;  // Return the pointer (ownership transfers to the caller)
}

// Function to copy the string to a global string
void copy_to_global(const char *s) {
    strncpy(global_string, s, sizeof(global_string) - 1);
    global_string[sizeof(global_string) - 1] = '\0';  // Ensure null termination
}

int main() {
    char *my_string = create_string(); // Takes ownership of the memory returned by create_string
    copy_to_global(my_string);         // Copy the string to the global variable

    // Use global_string here or elsewhere in your program
    // Example function calls or operations on global_string can be performed here

    free(my_string);  // Explicitly free the memory allocated in create_string
    my_string = NULL;  // Avoid dangling pointer by setting it to NULL after freeing

    return 0;
}
