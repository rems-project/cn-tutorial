// Tags: main, pointers, structs, alias, java, malloc

//#include <stdio.h>
#include <stdlib.h>

// Struct corresponding to the Java class C
typedef struct C {
    struct C *a; // Pointer to same struct type to mimic object reference
    int i;
} C;

/* Normal-behavior
 * @ requires true;
 * @ assignable a, i;
 * @ ensures a == NULL && i == 1;
 */
C* createC() {
    C* c = (C*) malloc(sizeof(C)); // Allocate memory for C
    c->a = NULL; // Initialize as null
    c->i = 1;    // Initialize i to 1
    return c;
}

// Struct corresponding to the Java class Alias
/* typedef struct Alias { */
/*     // No direct fields needed */
/* } Alias; */

/* Normal-behavior
 * @ requires true;
 * @ assignable nothing;
 * @ ensures result == 4;
 */
int m() {
    C* c = createC(); // Similar to 'C c = new C();'
    c->a = c;         // Alias to itself
    c->i = 2;         // Change i to 2
    int result = c->i + c->a->i; // Equivalent to 'return c.i + c.a.i;'
    free(c); // Clean up allocated memory
    return result;
}

int main() {
    /* Alias alias; // Instantiate Alias */
    int result = m(); // Call m and store result
    //printf("Result: %d\n", result); // Print the result
    return result;
}
