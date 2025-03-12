// Tags: main, arrays, java, malloc

/** Source
Examples translated to C from their original Java source in

Jacobs, Bart, Joseph Kiniry, and Martijn Warnier. "Java program
verification challenges." Formal Methods for Components and Objects:
First International Symposium, FMCO 2002, Leiden, The Netherlands,
November 5-8, 2002, Revised Lectures 1. Springer Berlin Heidelberg,
2003.

 */

/** Description
  
  Typical of Java is its systematic use of exceptions, via its statements for throwing
and catching. They require a suitable control flow semantics. Special care is
needed for the ‘finally’ part of a try-catch-finally construction. Figure 4 contains
a simple example (adapted from [17]) that combines many aspects. The subtle
point is that the assignment m+=10 in the finally block will still be executed,
despite the earlier return statements, but has no effect on the value that is
returned. The reason is that this value is bound earlier.
*/

//#include <stdio.h>
#include <stdlib.h>

int *ia; // Pointer to int, used as a dynamic array
int ia_length; // We need to manually keep track of the array's length

/* Normal-behavior
 * @ requires ia != NULL;
 * @ assignable ia[*];
 * @ ensures \forall int i; 0 <= i && i < ia_length => 
 *          (\old(ia[i]) < 0 && 
 *          (// i is the first position with negative value 
 *           \forall int j; 0 <= j && j < i => \old(ia[j]) >= 0))
 *          ? (ia[i] == -\old(ia[i]))
 *          : (ia[i] == \old(ia[i]));
 */
void negateFirst() {
    /* Maintaining i >= 0 && i <= ia_length &&
     * (\forall int j; 0 <= j && j < i =>
     *  (ia[j] >= 0 && ia[j] == \old(ia[j])))
     * @ decreasing ia_length - i;
     */
    for (int i = 0; i < ia_length; i++) {
        if (ia[i] < 0) {
            ia[i] = -ia[i]; // Negate the first negative value found
            break; // Exit after the first negation
        }
    }
}

int main()
  /*@ requires take vl0 = RW<int>(&ia_length)
      ensures take vp1 = RW<int>(&ia_length)
  @*/
  {
    // Example usage
    ia_length = 5; // Set the length of the array
    ia = (int*) malloc(ia_length * sizeof(int)); // Allocate memory for the array
    if (!ia) return 1; // Check for successful allocation

    // Initialize array with some values
    ia[0] = 10; ia[1] = 20; ia[2] = -30; ia[3] = 40; ia[4] = 50;

    negateFirst(); // Call the function

    // Print the array to see the results
    for (int i = 0; i < ia_length; i++) {
      //printf("%d ", ia[i]);
    }
    //printf("\n");

    free(ia); // Free the allocated memory
    return 0;
}
