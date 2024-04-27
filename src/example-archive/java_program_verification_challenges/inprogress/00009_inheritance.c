// Tags: main, pointers, structs, java, inheritance, complex

/** Source
Examples translated to C from their original Java source in

Jacobs, Bart, Joseph Kiniry, and Martijn Warnier. "Java program
verification challenges." Formal Methods for Components and Objects:
First International Symposium, FMCO 2002, Leiden, The Netherlands,
November 5-8, 2002, Revised Lectures 1. Springer Berlin Heidelberg,
2003.

Translation notes: We use structs to define classes, and other structs
to be the instances (as would objects in a OO language). This makes
the program complex, but simulates closely the initial intention of
the Java program.

 */

/** Title: Inheritance,  Overriding and Dynamic Types.

   Description: The program in Figure 9 is from [16] and was originally suggested by Joachim
van den Berg. On first inspection it looks like the method testQ will loop
forever.
The method testQ calls method m() from class C, which calls method m()
from class Inheritance, since ‘this’ has runtime-type Inheritance. Due to the
subtype semantics used in JML for inheritance, we cannot write specifications
for both of the m() methods with which we can reason. Therefore we can only
prove the specification of method testQ by using the method implementations.

*/

//#include <stdio.h>
#include <stdlib.h>

// Define an Exception type for handling errors explicitly
typedef enum {
    NO_EXCEPTION,
    EXCEPTION
} Exception;

typedef enum {
    TYPE_C,
    TYPE_INHERITANCE
} ObjectType;

// Forward declarations of struct types and function pointers
typedef struct C C;
typedef struct Inheritance Inheritance;

// Define the Instance struct with forward declaration resolved
typedef struct {
    void *object;
    ObjectType type;
} Instance;

// Function pointer types for methods and test function, now using the complete type of Instance
typedef Exception (*Method)(Instance);
typedef Exception (*TestMethod)(Instance);

// Define the base struct C
struct C {
    Method m; // Function pointer to methods that take an Instance
};

// Define the derived struct Inheritance
struct Inheritance {
    C base; // Inheritance via embedding
    Method m; // Specific function pointer for Inheritance's method
    TestMethod test; // Function pointer for the test method
};

// Generic method to decide dynamically which method to call
Exception generic_m(Instance instance) {
    switch (instance.type) {
        case TYPE_C:
            return ((C*)instance.object)->m(instance);
        case TYPE_INHERITANCE:
            return ((Inheritance*)instance.object)->m(instance);
        default:
            return EXCEPTION;
    }
}

// Implementation for base class method
Exception C_m(Instance instance) {
  return generic_m(instance);  // Recursive call
}

// Implementation for derived class method
Exception Inheritance_m(Instance instance) {
  return EXCEPTION;
}

// Test method in Inheritance that calls the base class method
Exception Inheritance_test(Instance instance)
{
    // Explicitly call the base class version of `m`
    if (instance.type == TYPE_INHERITANCE) {
        return ((Inheritance*)instance.object)->base.m(instance);
    }
    return EXCEPTION;
}

int main() {
    C c_instance = {C_m};
    Inheritance inh_instance = {{C_m}, Inheritance_m, Inheritance_test};

    Instance wrapped_c = {&c_instance, TYPE_C};
    Instance wrapped_inh = {&inh_instance, TYPE_INHERITANCE};

    // Testing Inheritance.test()
    Exception test_result = inh_instance.test(wrapped_inh);
    if (test_result == EXCEPTION) {
      //printf("Test method correctly threw an exception.\n");
    }

    return 0;
}

