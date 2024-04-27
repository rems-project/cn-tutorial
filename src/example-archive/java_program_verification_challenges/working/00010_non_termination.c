// Tags: main, java

/** Source
Examples translated to C from their original Java source in

Jacobs, Bart, Joseph Kiniry, and Martijn Warnier. "Java program
verification challenges." Formal Methods for Components and Objects:
First International Symposium, FMCO 2002, Leiden, The Netherlands,
November 5-8, 2002, Revised Lectures 1. Springer Berlin Heidelberg,
2003.

 */

/** Title: Non termination-A Program th a t does not Terminate.

   Description: The example in Figure 10 (due to Cees-Bart Breunesse)
shows a program that does not terminate.

   The specification asserts that the program does not terminate
normally or with an exception. The JML keyword diverges followed by
the predicate true indicates that the program fails to terminate. The
reader can easily see that this program does not terminate. Since Byte
.MAX.VALUE + 1 = Byte.MIN.VALUE the guard in the for loop will never
fail. Note that in order to verify this program both overflowing and
non-termination have to be modeled appropriately. ESC/Java does not
handle non-termination.

*/

//#include <stdio.h>
#include <limits.h>

/*
 * @ behavior
 * @ requires true;
 * @ assignable nothing;
 * @ ensures false;
 * @ signals (Exception) false;
 * @ diverges true;
 */
void m() {
    /* Using unsigned char to prevent overflow and ensure an infinite loop, 
       similar to the behavior in Java caused by byte overflow */
    for (unsigned char b = 0; ; b++) {
        // The loop will endlessly increment b without termination
        // In C, unsigned char naturally wraps around without causing overflow
        if (b == UCHAR_MAX) {
            // Reset to 0 explicitly to mimic Java's Byte overflow wrap-around
            b = -1; // Set to -1 because for loop will increment to 0 on the next iteration
        }
    }
}

int main() {
    m();  // Calling the method that never terminates
    return 0;
}
