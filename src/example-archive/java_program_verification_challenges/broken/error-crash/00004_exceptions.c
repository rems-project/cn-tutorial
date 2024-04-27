// Tags: main, java

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

NOTE: C doesn't handle exceptions. In the translation below, we use an
if statement to discriminate the input, making the example rather
trivial.

*/

//#include <stdio.h>

int m; // Global variable m

/* Normal-behavior
 * @ requires true;
 * @ assignable m;
 * @ ensures \result == ((d == 0) ? \old(m) : \old(m) / d)
 *           && m == \old(m) + 10;
 */
int returnfinally(int d)
  /*@ requires take vp0 = Owned<int>(&m);
               let m10 = (i64)vp0 + 10i64 ;
               m10 <= 2147483647i64
      ensures take vp1 = Owned<int>(&m)
  @*/
  {
    int result;

    if (d == 0) {
        result = m; // Handle division by zero case
    } else {
        result = m / d; // Normal division
    }

    m += 10; // This corresponds to the 'finally' block in Java, executed regardless of exception

    return result;
}

int main()
  /*@ requires take vp0 = Owned<int>(&m)
      ensures take vp1 = Block<int>(&m);
	      return == 0i32
  @*/
{
    m = 20; // Initialize m
    int d = 0; // Example divisor, change this value to test different paths
    //printf("Result: %d\n", returnfinally(d));
    //printf("Updated m: %d\n", m);
    return 0;
}
