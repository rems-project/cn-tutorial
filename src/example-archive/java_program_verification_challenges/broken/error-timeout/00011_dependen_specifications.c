// Tags: main, loops, java, arithmetic

/** Source
Examples translated to C from their original Java source in

Jacobs, Bart, Joseph Kiniry, and Martijn Warnier. "Java program
verification challenges." Formal Methods for Components and Objects:
First International Symposium, FMCO 2002, Leiden, The Netherlands,
November 5-8, 2002, Revised Lectures 1. Springer Berlin Heidelberg,
2003.

 */

/** Title: Dependent Specifications and Integral Types.

   Description: The final example exemplifies two commonplace
complications in reasoning about “real world” Java.  Representations
of integral types (e.g., int, short, byte, etc.) in Java are finite. A
review of annotated programs that use integral types indicates that
specifications are often written with infinite numeric models in mind
[7]. Programmers seem to think about the issues of overflow (and
underflow, in the case of floating point numbers) in program code, but
not in specifications.  Additionally, it is often the case that
specifications use functional method invocations. Methods which have
no side-effects in the program are called called “pure” methods in JML
and “queries” in the Eiffel and UML communities7.  The example in
Figure 11 highlights both complications, as it uses method invocations
in a specification and integral values that can potentially overflow.
The method isqrt(), which computes an integer square root of its
input, is inspired by a specification (see Figure 12) of a similar
function included with early JML releases [20].

Note that the iabsQ method in Figure 11 is used in the specification of
isqrtO to stipulate that both the negative and the positive square root are
an acceptable return value, as all we care about is its magnitude. Actually, our
implementation of is q rtQ only computes the positive integer square root.

... [see more in the paper].

*/

#include <limits.h>
//#include <stdio.h>

/* Normal-behavior
 * @ requires true;
 * @ assignable nothing;
 * @ ensures \result == ((x >= 0 || x == INT_MIN) ? x : -x);
 */
int iabs(int x)
{
    if (x < 0) return -x;
    else return x;
}

 /* Normal-behavior
 * @ requires x >= 0 && x <= 2147390966;
 * @ assignable nothing;
 * @ ensures iabs(\result) < 46340 &&
 *          \result * \result <= x &&
 *          x < (iabs(\result) + 1) * (iabs(\result) + 1);
 */
int isqrt(int x)
  /*@ requires 0i32 <= x ; x<= 2147390966i32; 
      ensures true; 
  @*/
{
    int count = 0, sum = 1;

    /* Maintaining 0 <= count &&
     * @ count < 46340 &&
     * @ count * count <= x &&
     * @ sum == (count + 1) * (count + 1);
     * @ decreasing x - count;
     */
    while (sum <= x)
    /*@ inv 0i32 <= count;
            count < 46340i32;
	    count * count <= x;
	    sum == (count + 1i32 ) * (count + 1i32);
	    sum <= x + 2i32 *count+1i32; 
      @*/
    {
        count++;
        sum += 2 * count + 1;
    }
    return count;
}

int main() {
    int num = 10;
    int result = isqrt(num);
    //printf("The integer square root of %d is %d\n", num, result);
    return 0;
}
