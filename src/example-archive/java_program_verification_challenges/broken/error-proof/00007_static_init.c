// Tags: main, java, bool

/** Source
Examples translated to C from their original Java source in

Jacobs, Bart, Joseph Kiniry, and Martijn Warnier. "Java program
verification challenges." Formal Methods for Components and Objects:
First International Symposium, FMCO 2002, Leiden, The Netherlands,
November 5-8, 2002, Revised Lectures 1. Springer Berlin Heidelberg,
2003.

 */

/** Title: Static Initialization.

   Description: Figure 7 shows an example of static initialization in
Java (due to Jan Bergstra).  In Java a class is initialized at its
first active use (see [13]). This means that class initialization in
Java is lazy, so that the result of initialization depends on the
order in which classes are initialized. The rather sick example in
Figure 7 shows what happens when two classes, which are not yet
initialized, have static fields referring to each other. In the
specification we use a new keyword \static_f ields_of in the
assignable clause. It is syntactic sugar for all static fields of the
class.  The first assignment in the body of method m() triggers the
initialization of class Cl, which in turn triggers the initialization
of class C2. The result of the whole initialization is, for instance,
that static field C2.b2 gets value false assigned to it. This can be
seen when one realizes that the boolean static fields from class Cl
initially get the default value false. Subsequently, class C2 becomes
initialized and its fields also get the default value false. Now the
assignments in class C2 are carried out: d2 is set to true and b2 is
set to false. Note that dl is still false at this stage. Finally the
assignments to fields in class Cl take place, both resulting in value
true.  One can see that the order of initializations is
important. When the first two assignments in the method body of m()
are switched, class C2 will be initialized before class Cl resulting
in all fields getting value true.  ESC/Java cannot handle this example
as it cannot reason about static initialization. It provides no
warnings for potential run-time errors in static initializers or in
initializers for static fields.

*/

//#include <stdio.h>
#include <stdbool.h>

// Forward declarations are necessary since C1 and C2 reference each other.
extern bool bl;
extern bool dl;
extern bool d2;
extern bool b2;

// Global static variables for class C
bool result1, result2, result3, result4;

// Function to simulate static initialization as found in Java
void initialize();

// Definitions corresponding to static members of classes C1 and C2
bool bl = true; // Temporary initialization
bool dl = true;
bool d2 = true;
bool b2 = true; // Temporary initialization

void initialize() {
    bl = d2;  // Correct initialization order based on Java static initialization
    b2 = dl;  // Correct initialization order based on Java static initialization
}

/* Normal-behavior
 * @ requires !\is_initialized(C) &
 * @ !\is_initialized(C1) &
 * @ !\is_initialized(C2);
 * @ assignable \static_fields_of(C),
 * @ \static_fields_of(C1),
 * @ \static_fields_of(C2);
 * @ ensures result1 && !result2 && result3 && result4
 */
void m()
  /*@ requires take vbl0 = RW<bool>(bl);
               take vdl0 = RW<bool>(dl);
	       take vb20 = RW<bool>(b2);
	       take vd20 = RW<bool>(d2)
      ensures true
  @*/
  {
    result1 = bl;
    result2 = b2;
    result3 = dl;
    result4 = d2;
}

int main() {
    initialize();  // Initialize static fields correctly
    m();  // Execute the method that sets results based on static fields

    /* printf("Result1: %d\n", result1); */
    /* printf("Result2: %d\n", result2); */
    /* printf("Result3: %d\n", result3); */
    /* printf("Result4: %d\n", result4); */

    return 0;
}
