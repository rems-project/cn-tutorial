// Tags: main, java, bool

/** Source
Examples translated to C from their original Java source in

Jacobs, Bart, Joseph Kiniry, and Martijn Warnier. "Java program
verification challenges." Formal Methods for Components and Objects:
First International Symposium, FMCO 2002, Leiden, The Netherlands,
November 5-8, 2002, Revised Lectures 1. Springer Berlin Heidelberg,
2003.

 */

/** Description
  
  One of the most common abstractions in program verification is to
omit sideeffects from expressions in the programming language. This is
a serious restriction. Figure 2 contains a nice and simple example
from [4] where such side-effects play a crucial rôle, in combination
with the logical operators. Recall th at in Java there are two
disjunctions (I and I I) and two conjunctions (& and &&). The double
versions ( I I and &&) are the so-called conditional operators: their
second argument is only evaluated if the first one is false (for II)
or true (for &&).

In case the field b in Figure 2 is true, method m() yields f () V -if
() = false and -if () A f () = true, going against standard logical
rules.  The verification of the specification for method m() may use
either the implementation or the specification of f ().
*/


#include <stdbool.h>
//#include <stdio.h>

bool b = true;
bool result1, result2;

/* Normal-behavior
 * @ requires true;
 * @ assignable b;
 * @ ensures b == !\old(b) && \result == b;
 */
bool f() {
    bool old_b = b;  // Capture the old value of b to use in logging or future conditions
    b = !b;          // Toggle b
    return b;        // Return the new value of b
}

/* Normal-behavior
 * @ requires true;
 * @ assignable b, result1, result2;
 * @ ensures (\old(b) => (result1 && result2)) &&
 *           (!\old(b) => (result1 && result2));
 */
void m() {
    bool old_b = b;     // Capture the old value of b for condition check
    result1 = f() || !f();  // Call f, toggle b, then call f again (consider the effect of !f() on b)
    result2 = !f() && f();  // Similarly toggle b twice considering the effect on result2
}

int main()
  /*@ requires take vr0 = Block<bool>(result1);
               take vr0 = Block<bool>(result2)
      ensures take vp1 = Block<bool>(result1);
              take vb1 = Block<bool>(result2)
  @*/
  {
    m();  // Execute the function m
    //printf("Result1: %d, Result2: %d\n", result1, result2);  // Print the results
    int ret = (int)result1 + (int)result2;
    return ret;
}
